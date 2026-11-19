// stream.cpp: byte-stream devices (see px4_shim.h), for modules that talk over a serial port
// (mavlink started with -d DEVICE). A device named in px4.txt (`stream NAME DEVICE WORDS`) is a
// pair of FIFOs inside the process, behind the POSIX calls a serial driver answers: access, open,
// close, read, write, poll, tcgetattr, tcsetattr. The module's code calls these unchanged; here they are
// defined for the module's objects and pass every other file descriptor on to libSystem.
//
// Per step the harness feeds the receive FIFO with the input record's bytes (<NAME>_rx_len bytes
// packed little-endian into the u32 words <NAME>_rx_<i>) and takes up to 4*WORDS bytes from the
// transmit FIFO into <NAME>_tx_len / <NAME>_tx_<i>. Each FIFO holds STREAM_BUFFER bytes, as a
// UART driver's buffers do: a byte that arrives on a full receive FIFO is dropped and counted
// (<NAME>_rx_dropped); a write on a full transmit FIFO writes what fits and returns that count,
// so the module sees a short write, as on a busy serial port. <NAME>_tx_pending is what remains
// in the transmit FIFO after the step (sent at the next steps).
//
// A read never blocks (the port is read after poll, as mavlink's receiver does); poll on the device
// with no byte waiting blocks the calling task until bytes arrive or its timeout passes on the
// harness clock (tasks.cpp).
#include "px4_shim.h"

#include <dlfcn.h>
#include <errno.h>
#include <fcntl.h>
#include <poll.h>
#include <stdarg.h>
#include <string.h>
#include <termios.h>
#include <unistd.h>
#include <deque>
#include <string>
#include <vector>

#include <drivers/drv_hrt.h>

namespace
{
constexpr size_t STREAM_BUFFER = 4096;

struct Device {
	std::string path;
	std::deque<uint8_t> rx, tx;
	uint32_t rx_dropped{0};
	int fd{-1};             // the descriptor handed out (a real one, on /dev/null, to keep numbers unique)
	struct termios tio {};
};

std::vector<Device *> devices;

Device *by_fd(int fd)
{
	if (fd < 0) {
		return nullptr;
	}

	for (Device *d : devices) {
		if (d->fd == fd) {
			return d;
		}
	}

	return nullptr;
}

template<typename F> F real(const char *name)
{
	return reinterpret_cast<F>(dlsym(RTLD_NEXT, name));
}
} // namespace

extern "C" {

int open(const char *path, int flags, ...)
{
	for (Device *d : devices) {
		if (d->path == path) {
			if (d->fd < 0) {
				d->fd = real<int (*)(const char *, int, ...)>("open")("/dev/null", O_RDWR);
			}

			return d->fd;
		}
	}

	va_list a;
	va_start(a, flags);
	const int mode = (flags & O_CREAT) ? va_arg(a, int) : 0;
	va_end(a);
	return real<int (*)(const char *, int, ...)>("open")(path, flags, mode);
}

int access(const char *path, int mode)
{
	for (Device *d : devices) {
		if (d->path == path) {
			return 0;
		}
	}

	return real<int (*)(const char *, int)>("access")(path, mode);
}

int close(int fd)
{
	if (Device *d = by_fd(fd)) {
		d->fd = -1;
	}

	return real<int (*)(int)>("close")(fd);
}

ssize_t read(int fd, void *buf, size_t n)
{
	Device *d = by_fd(fd);

	if (d == nullptr) {
		return real<ssize_t (*)(int, void *, size_t)>("read")(fd, buf, n);
	}

	if (d->rx.empty()) {
		errno = EAGAIN;
		return -1;
	}

	size_t k = 0;

	for (; k < n && !d->rx.empty(); k++) {
		static_cast<uint8_t *>(buf)[k] = d->rx.front();
		d->rx.pop_front();
	}

	return (ssize_t)k;
}

ssize_t write(int fd, const void *buf, size_t n)
{
	Device *d = by_fd(fd);

	if (d == nullptr) {
		return real<ssize_t (*)(int, const void *, size_t)>("write")(fd, buf, n);
	}

	size_t k = 0;

	for (; k < n && d->tx.size() < STREAM_BUFFER; k++) {
		d->tx.push_back(static_cast<const uint8_t *>(buf)[k]);
	}

	if (k == 0 && n > 0) {
		errno = EAGAIN;
		return -1;
	}

	return (ssize_t)k;
}

int poll(struct pollfd *fds, nfds_t nfds, int timeout)
{
	bool ours = false;

	for (nfds_t i = 0; i < nfds; i++) {
		ours = ours || by_fd(fds[i].fd) != nullptr;
	}

	if (!ours) {
		return real<int (*)(struct pollfd *, nfds_t, int)>("poll")(fds, nfds, timeout);
	}

	auto check = [fds, nfds]() {
		int n = 0;

		for (nfds_t i = 0; i < nfds; i++) {
			Device *d = by_fd(fds[i].fd);
			fds[i].revents = 0;

			if (d) {
				if ((fds[i].events & POLLIN) && !d->rx.empty()) {
					fds[i].revents |= POLLIN;
				}

				if ((fds[i].events & POLLOUT) && d->tx.size() < STREAM_BUFFER) {
					fds[i].revents |= POLLOUT;
				}
			}

			n += fds[i].revents ? 1 : 0;
		}

		return n;
	};

	const int n = check();

	if (n > 0 || timeout == 0) {
		return n;
	}

	const uint64_t now = hrt_absolute_time();
	px4_shim::wait_until([&check] { return check() > 0; }, timeout < 0 ? UINT64_MAX : now + (uint64_t)timeout * 1000);
	return check();
}

int tcgetattr(int fd, struct termios *t)
{
	if (Device *d = by_fd(fd)) {
		*t = d->tio;
		return 0;
	}

	return real<int (*)(int, struct termios *)>("tcgetattr")(fd, t);
}

int tcsetattr(int fd, int action, const struct termios *t)
{
	if (Device *d = by_fd(fd)) {
		d->tio = *t;
		return 0;
	}

	return real<int (*)(int, int, const struct termios *)>("tcsetattr")(fd, action, t);
}

} // extern "C"

// ---- the harness side
namespace px4_shim
{
void stream_register(const char *path)
{
	Device *d = new Device();
	d->path = path;
	devices.push_back(d);
}

void stream_inject(const char *path, const uint32_t *words, uint32_t len, uint32_t max_words)
{
	for (Device *d : devices) {
		if (d->path == path) {
			const uint32_t n = len < 4 * max_words ? len : 4 * max_words;

			for (uint32_t i = 0; i < n; i++) {
				if (d->rx.size() < STREAM_BUFFER) {
					d->rx.push_back((uint8_t)(words[i / 4] >> (8 * (i % 4))));

				} else {
					d->rx_dropped++;
				}
			}
		}
	}
}

void stream_collect(const char *path, uint32_t *words, uint32_t max_words, uint32_t *len, uint32_t *pending,
		    uint32_t *rx_dropped)
{
	memset(words, 0, 4 * max_words);
	*len = *pending = *rx_dropped = 0;

	for (Device *d : devices) {
		if (d->path == path) {
			uint32_t n = 0;

			for (; n < 4 * max_words && !d->tx.empty(); n++) {
				words[n / 4] |= (uint32_t)d->tx.front() << (8 * (n % 4));
				d->tx.pop_front();
			}

			*len = n;
			*pending = (uint32_t)d->tx.size();
			*rx_dropped = d->rx_dropped;
		}
	}
}
} // namespace px4_shim
