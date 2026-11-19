// cpp2lean-options: --boundary Nav --boundary-query Nav::armed
// cpp2lean rejection test (phase 3, AC_AttitudeControl and AC_PosControl constructs): the constructs
// added for them, used outside their limits. Each line marked expect-reject must be reported
// (reject_phase3c.expected), and no other line.

class V2c {
public:
    float x, y;
    void zero() { x = 0; y = 0; }
};

class V3c {
public:
    float x, y, z;
    V2c &xy() { return *(V2c *)this; }
};

class Nav {
public:
    float trim;
    bool on;
    bool armed() { return on; }
    bool busy() { return !on; }
};

class User {
public:
    User(Nav &nav) : _nav(nav) {}
    // accepted: a non-const getter named by --boundary-query
    bool ok() { return _nav.armed(); }
    // a non-const getter not named by --boundary-query: a call that may change the boundary
    bool waiting() { return _nav.busy(); }  // expect-reject
    // a local const reference to a data member of a boundary object (only references to boundary
    // reads, i.e. results of const calls, are copies)
    float trim() { const float &t = _nav.trim; return t; }  // expect-reject
    // accepted: writes through the view of a member
    void clear() { _p.xy().zero(); }
    // an accessor returning a reference that is not one member (a choice of two): a non-const call
    // on what it returns is not a call on a known member
    V2c &pick() { return _a ? _p.xy() : _q.xy(); }
    void clear_pick() { pick().zero(); }  // expect-reject
private:
    Nav &_nav;
    V3c _p;
    V3c _q;
    bool _a;
};
