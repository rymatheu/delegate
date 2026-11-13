// cpp2lean difftest environment of examples/navigate.cpp (C++ side only): the clock, the boundary
// (--boundary-fn clk::now_ms), set from the driver's input `navigator.now_ms`.
uint32_t nav_now;
uint32_t clk::now_ms() { return nav_now; }
