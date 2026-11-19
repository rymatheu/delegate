// bus.cpp: the message bus stand-in (see px4_shim.h).
//
// PX4's uORB client classes are compiled unmodified; they reach the bus through uORB::Manager's
// static functions and the orb_* C functions, which are defined here instead of in uORBManager.cpp,
// uORBDeviceNode.cpp and uORB.cpp. One node per (topic, instance) holds a queue of o_queue messages
// and a generation counter, with the semantics of uORB::DeviceNode (write, copy,
// get_initial_generation, updates_available); a write calls every registered callback, which for a
// SubscriptionCallbackWorkItem schedules the work item. Nothing runs concurrently, so no locks.
//
// The harness side: inject() publishes a message as a publisher outside the module would;
// collect() reads the latest message on a node and says whether one was published since the last
// collect. Nodes are never freed: a reset clears them in place, so handles kept in static storage
// by library code (events.cpp keeps its event publication) stay valid across a re-init.
#include "px4_shim.h"

#include <stdlib.h>
#include <string.h>
#include <vector>
#include <algorithm>

#include <uORB/uORBManager.hpp>
#include <uORB/SubscriptionCallback.hpp>
#include <uORB/SubscriptionInterval.hpp>
#include <uORB/topics/uORBTopics.hpp>

namespace
{
struct Node {
	const orb_metadata *meta;
	uint8_t instance;
	uint8_t *data;          // o_queue messages of o_size bytes
	unsigned generation;    // messages written so far
	bool advertised;
	bool data_valid;
	unsigned collected;     // generation at the last collect()
	unsigned hidden;        // messages up to this generation are not shown to the harness
	// a tap (tap()): every message written on the node this step, for an output port with more
	// slots than the topic's queue (a mirror must see each message, not the latest)
	unsigned tap_slots;
	unsigned tap_count;
	unsigned tap_lost;
	std::vector<uint8_t> tap_data;
	std::vector<uORB::SubscriptionCallback *> callbacks;
};

Node *nodes[ORB_TOPICS_COUNT][ORB_MULTI_MAX_INSTANCES];
unsigned writes = 0;    // messages written on the bus so far

Node *node_for(const orb_metadata *meta, uint8_t instance)
{
	if (meta == nullptr || meta->o_id >= ORB_TOPICS_COUNT || instance >= ORB_MULTI_MAX_INSTANCES) {
		return nullptr;
	}

	Node *&n = nodes[meta->o_id][instance];

	if (n == nullptr) {
		n = new Node{};
		n->meta = meta;
		n->instance = instance;
		n->data = static_cast<uint8_t *>(calloc(meta->o_queue ? meta->o_queue : 1, meta->o_size));
	}

	return n;
}

// uORB::DeviceNode::write
void write(Node *n, const void *data)
{
	const unsigned q = n->meta->o_queue ? n->meta->o_queue : 1;
	const unsigned g = n->generation++;
	writes++;

	if (n->tap_slots > 0) {
		if (n->tap_count < n->tap_slots) {
			memcpy(n->tap_data.data() + n->meta->o_size * n->tap_count, data, n->meta->o_size);
			n->tap_count++;

		} else {
			n->tap_lost++;
		}
	}
	memcpy(n->data + n->meta->o_size * (g % q), data, n->meta->o_size);
	n->data_valid = true;
	// callbacks may unregister themselves; iterate over a copy
	const std::vector<uORB::SubscriptionCallback *> cbs = n->callbacks;

	for (uORB::SubscriptionCallback *cb : cbs) {
		cb->call();
	}
}

bool in_range(unsigned left, unsigned value, unsigned right)
{
	if (right > left) {
		return (left <= value) && (value <= right);
	} else {    // overflow
		return (value >= left) || (value <= right);
	}
}

// uORB::DeviceNode::copy
bool copy(Node *n, void *dst, unsigned &generation)
{
	if (dst == nullptr || !n->data_valid) {
		return false;
	}

	const unsigned q = n->meta->o_queue ? n->meta->o_queue : 1;

	if (q == 1) {
		memcpy(dst, n->data, n->meta->o_size);
		generation = n->generation;
		return true;
	}

	const unsigned current = n->generation;

	if (current == generation) {
		--generation;    // nothing new: read the latest again
	}

	if (!in_range(current - q, generation, current - 1)) {
		generation = current - q;    // too far behind: messages lost
	}

	memcpy(dst, n->data + n->meta->o_size * (generation % q), n->meta->o_size);
	++generation;
	return true;
}
} // namespace

// ---- uORB::Manager: the functions PX4's client classes call
uORB::Manager *uORB::Manager::_Instance = nullptr;

uORB::Manager::Manager() {}
uORB::Manager::~Manager() {}

bool uORB::Manager::initialize()
{
	if (_Instance == nullptr) {
		_Instance = new uORB::Manager();
	}

	return _Instance != nullptr;
}

bool uORB::Manager::orb_device_node_exists(ORB_ID orb_id, uint8_t instance)
{
	const orb_metadata *meta = get_orb_meta(orb_id);
	return meta && instance < ORB_MULTI_MAX_INSTANCES && nodes[meta->o_id][instance] &&
	       nodes[meta->o_id][instance]->advertised;
}

void *uORB::Manager::orb_add_internal_subscriber(ORB_ID orb_id, uint8_t instance, unsigned *initial_generation)
{
	Node *n = node_for(get_orb_meta(orb_id), instance);

	if (n) {
		*initial_generation = n->generation - (n->data_valid ? 1 : 0);   // get_initial_generation
	}

	return n;
}

void uORB::Manager::orb_remove_internal_subscriber(void *node_handle) { (void)node_handle; }

uint8_t uORB::Manager::orb_get_queue_size(const void *node_handle)
{
	return static_cast<const Node *>(node_handle)->meta->o_queue;
}

bool uORB::Manager::orb_data_copy(void *node_handle, void *dst, unsigned &generation, bool only_if_updated)
{
	Node *n = static_cast<Node *>(node_handle);

	if (!n->advertised) {
		return false;
	}

	if (only_if_updated && n->generation == generation) {
		return false;
	}

	return copy(n, dst, generation);
}

bool uORB::Manager::register_callback(void *node_handle, SubscriptionCallback *callback_sub)
{
	Node *n = static_cast<Node *>(node_handle);

	if (std::find(n->callbacks.begin(), n->callbacks.end(), callback_sub) == n->callbacks.end()) {
		n->callbacks.push_back(callback_sub);
	}

	return true;
}

void uORB::Manager::unregister_callback(void *node_handle, SubscriptionCallback *callback_sub)
{
	Node *n = static_cast<Node *>(node_handle);
	n->callbacks.erase(std::remove(n->callbacks.begin(), n->callbacks.end(), callback_sub), n->callbacks.end());
}

uint8_t uORB::Manager::orb_get_instance(const void *node_handle)
{
	return static_cast<const Node *>(node_handle)->instance;
}

unsigned uORB::Manager::updates_available(const void *node_handle, unsigned last_generation)
{
	const Node *n = static_cast<const Node *>(node_handle);
	return n->advertised ? n->generation - last_generation : 0;
}

bool uORB::Manager::is_advertised(const void *node_handle)
{
	return static_cast<const Node *>(node_handle)->advertised;
}

int uORB::Manager::orb_publish(const struct orb_metadata *meta, orb_advert_t handle, const void *data)
{
	(void)meta;

	if (handle == nullptr) {
		return PX4_ERROR;
	}

	write(static_cast<Node *>(handle), data);
	return PX4_OK;
}

int uORB::Manager::orb_unadvertise(orb_advert_t handle)
{
	if (handle) {
		static_cast<Node *>(handle)->advertised = false;
	}

	return PX4_OK;
}

// ---- the orb_* C API (uORB.cpp)
orb_advert_t orb_advertise_multi(const struct orb_metadata *meta, const void *data, int *instance)
{
	Node *n = nullptr;

	if (instance == nullptr) {
		n = node_for(meta, 0);

	} else {
		// the first instance without a publisher (DeviceMaster::advertise)
		for (int i = 0; i < ORB_MULTI_MAX_INSTANCES; i++) {
			Node *c = node_for(meta, i);

			if (c && !c->advertised) {
				n = c;
				*instance = i;
				break;
			}
		}
	}

	if (n == nullptr) {
		return nullptr;
	}

	n->advertised = true;

	if (data) {
		write(n, data);
	}

	return n;
}

orb_advert_t orb_advertise(const struct orb_metadata *meta, const void *data)
{
	return orb_advertise_multi(meta, data, nullptr);
}

int orb_unadvertise(orb_advert_t handle) { return uORB::Manager::orb_unadvertise(handle); }

int orb_publish(const struct orb_metadata *meta, orb_advert_t handle, const void *data)
{
	return uORB::Manager::orb_publish(meta, handle, data);
}

int orb_exists(const struct orb_metadata *meta, int instance)
{
	return (meta && instance >= 0 && instance < ORB_MULTI_MAX_INSTANCES && nodes[meta->o_id][instance] &&
		nodes[meta->o_id][instance]->advertised) ? PX4_OK : PX4_ERROR;
}

int orb_group_count(const struct orb_metadata *meta)
{
	int n = 0;

	for (int i = 0; i < ORB_MULTI_MAX_INSTANCES; i++) {
		if (orb_exists(meta, i) == PX4_OK) {
			n++;
		}
	}

	return n;
}

uint8_t orb_get_queue_size(const struct orb_metadata *meta) { return meta ? meta->o_queue : 0; }

// the subscriber side of the C API (orb_subscribe ... orb_copy, orb_set_interval), for code that
// uses it (SubscriptionCallback::registerCallback's fallback, navigator, commander, dataman): as in
// uORBDeviceNode.cpp, each handle is a uORB::SubscriptionInterval (PX4's own class): orb_copy is its
// copy(), orb_check its updated(), orb_set_interval its interval, and px4_poll (tasks.cpp) reports
// POLLIN when updated() is true (uORB::DeviceNode::poll_state). Handles index a table.
namespace
{
std::vector<uORB::SubscriptionInterval *> csubs;

uORB::SubscriptionInterval *csub(int handle)
{
	return (handle >= 0 && handle < (int)csubs.size()) ? csubs[handle] : nullptr;
}
}

int orb_subscribe_multi(const struct orb_metadata *meta, unsigned instance)
{
	if (node_for(meta, instance) == nullptr) {
		return PX4_ERROR;
	}

	uORB::SubscriptionInterval *s = new uORB::SubscriptionInterval(meta, 0, instance);
	s->subscribe();
	csubs.push_back(s);
	return (int)csubs.size() - 1;
}

int orb_subscribe(const struct orb_metadata *meta) { return orb_subscribe_multi(meta, 0); }

int orb_unsubscribe(int handle)
{
	if (csub(handle)) {
		delete csubs[handle];
		csubs[handle] = nullptr;
	}

	return PX4_OK;
}

int orb_copy(const struct orb_metadata *meta, int handle, void *buffer)
{
	(void)meta;
	uORB::SubscriptionInterval *s = csub(handle);
	return (s && s->copy(buffer)) ? PX4_OK : PX4_ERROR;
}

int orb_check(int handle, bool *updated)
{
	uORB::SubscriptionInterval *s = csub(handle);
	*updated = false;

	if (s == nullptr) {
		return PX4_ERROR;
	}

	*updated = s->updated();
	return PX4_OK;
}

int orb_set_interval(int handle, unsigned interval)
{
	uORB::SubscriptionInterval *s = csub(handle);

	if (s == nullptr) {
		return PX4_ERROR;
	}

	s->set_interval_ms(interval);
	return PX4_OK;
}

int orb_get_interval(int handle, unsigned *interval)
{
	uORB::SubscriptionInterval *s = csub(handle);

	if (s == nullptr) {
		return PX4_ERROR;
	}

	*interval = s->get_interval_us() / 1000;
	return PX4_OK;
}

// ---- the harness side
namespace px4_shim
{
void bus_reset()
{
	uORB::Manager::initialize();
	csubs.clear();    // the handles of a previous case (their objects are left: code may hold them)

	for (auto &row : nodes) {
		for (Node *n : row) {
			if (n) {
				memset(n->data, 0, (n->meta->o_queue ? n->meta->o_queue : 1) * n->meta->o_size);
				n->generation = 0;
				n->advertised = false;
				n->data_valid = false;
				n->collected = 0;
				n->hidden = 0;
				n->tap_slots = n->tap_count = n->tap_lost = 0;
				n->tap_data.clear();
				n->callbacks.clear();
			}
		}
	}
}

void inject(const orb_metadata *meta, uint8_t instance, const void *data)
{
	Node *n = node_for(meta, instance);
	n->advertised = true;
	write(n, data);
}

bool collect(const orb_metadata *meta, uint8_t instance, void *data, size_t size)
{
	Node *n = node_for(meta, instance);
	memset(data, 0, size);

	if (!n->data_valid || n->generation == n->hidden) {
		n->collected = n->generation;
		return false;
	}

	const unsigned q = n->meta->o_queue ? n->meta->o_queue : 1;
	memcpy(data, n->data + n->meta->o_size * ((n->generation - 1) % q), n->meta->o_size);
	const bool fresh = n->generation != n->collected;
	n->collected = n->generation;
	return fresh;
}

unsigned bus_writes() { return writes; }

void tap(const orb_metadata *meta, uint8_t instance, unsigned slots)
{
	Node *n = node_for(meta, instance);
	n->tap_slots = slots;
	n->tap_count = n->tap_lost = 0;
	n->tap_data.assign((size_t)slots * meta->o_size, 0);
}

void collect_tap(const orb_metadata *meta, uint8_t instance, void *data, size_t size, unsigned slots,
		 unsigned *count, unsigned *lost)
{
	Node *n = node_for(meta, instance);
	memset(data, 0, size * slots);
	const unsigned k = n->tap_count < slots ? n->tap_count : slots;

	for (unsigned i = 0; i < k; i++) {
		memcpy(static_cast<uint8_t *>(data) + size * i, n->tap_data.data() + n->meta->o_size * i, n->meta->o_size);
	}

	*count = k;
	*lost = n->tap_lost + (n->tap_count - k);
	n->tap_count = n->tap_lost = 0;
	n->collected = n->generation;
}

void hide_published()
{
	for (auto &row : nodes) {
		for (Node *n : row) {
			if (n) {
				n->hidden = n->generation;
				n->collected = n->generation;
				n->tap_count = n->tap_lost = 0;
			}
		}
	}
}

bool orb_fd_updated(int handle)
{
	uORB::SubscriptionInterval *s = csub(handle);
	return s != nullptr && s->updated();
}

// the messages published on the node since the last collect, oldest first: as a subscriber with a
// queue of `slots` reading once per step, the newest min(new, o_queue, slots) messages; the older
// ones are lost (uORB::DeviceNode::copy for a subscriber that fell behind)
void collect_queue(const orb_metadata *meta, uint8_t instance, void *data, size_t size, unsigned slots,
		   unsigned *count, unsigned *lost)
{
	Node *n = node_for(meta, instance);
	memset(data, 0, size * slots);
	const unsigned q = n->meta->o_queue ? n->meta->o_queue : 1;
	const unsigned from = n->collected > n->hidden ? n->collected : n->hidden;
	const unsigned fresh = n->data_valid ? n->generation - from : 0;
	unsigned k = fresh < q ? fresh : q;
	k = k < slots ? k : slots;

	for (unsigned i = 0; i < k; i++) {
		const unsigned g = n->generation - k + i;
		memcpy(static_cast<uint8_t *>(data) + size * i, n->data + n->meta->o_size * (g % q), n->meta->o_size);
	}

	*count = k;
	*lost = fresh - k;
	n->collected = n->generation;
}
} // namespace px4_shim
