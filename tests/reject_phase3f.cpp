// cpp2lean-options: --world --world-pointers --pointer-params --runtime-loops --general-loops --semaphores Semaphore
// cpp2lean rejection test (Phase 3: World pointers, heap slots, functors, semaphores): the limits of
// --world-pointers and --semaphores. Each line marked expect-reject must be reported, and nothing else.
#include <cstdint>
#include <cstdlib>
#include <new>

class Semaphore {
public:
    bool take(uint32_t timeout_ms) { return true; }
    bool give() { return true; }
    uint32_t count() const { return 0; }
};

class Part {
public:
    virtual ~Part() {}
    virtual float value() const { return _v; }
    float _v;
};

class PartA : public Part {
public:
    float value() const override { return _v + 1.0f; }
};

class PartB : public Part {
public:
    float value() const override { return _v * 2.0f; }
};

class Orphan {
public:
    float get() const { return _x; }
    float _x;
};

class Cell {
public:
    Cell() {}
    float _y;
};

class Point {
public:
    // `this` as a value in a class without a file-scope or heap object
    const Point *self() const { return this; }          // expect-reject
    float x;
};

class Holder;

class Leaf {
public:
    explicit Leaf(Holder &h);
    float _z;
};

class Holder {
public:
    void build() {
        parts[0] = new PartA();
        parts[1] = new PartB();
        leaf = new Leaf(*this);
    }
    // a member read through a pointer that may point to objects of two classes
    float first() const { return parts[0]->_v; }                // expect-reject
    // a call through a pointer to a class of which the program has no object
    float orphan() const { return lost->get(); }                // expect-reject
    // placement new somewhere other than the slots of its heap objects
    void place() { new (&cell) Cell(); }                         // expect-reject
    // memory whose size is not `sizeof(C) * k`
    void reserve() { cells = (Cell *)malloc(64); }               // expect-reject
    // a semaphore member function with a result other than success
    uint32_t users() const { return _sem.count(); }            // expect-reject
    // a pointer to a class made from a pointer to something else
    void alias() { cells = (Cell *)&_w; }                        // expect-reject
    float poke() { return _w += 1.0f; }
    Part *parts[2];
    Orphan *lost;
    Cell cell;
    Cell *cells;
    Leaf *leaf;
    float _w;
    Semaphore _sem;
};

// a heap object's constructor that reaches the object being constructed
Leaf::Leaf(Holder &h) {
    h.leaf = this;
    h.poke();
    _z = h.leaf->_z;                                            // expect-reject
}

Holder holder;
