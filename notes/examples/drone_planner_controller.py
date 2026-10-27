"""One delegation: altitude planner -> altitude controller of a drone.

Signals (discrete time, horizon N):
  environment inputs   z      true/estimated altitude      (read by the controller)
                       zg     goal altitude                (read by the planner)
  internal wire        r      reference altitude           planner -> controller
  output               u      vertical velocity command    controller -> outside

Query (A, G) on the segment:
  A = []( 0 <= z <= ZMAX )  /\  []( M <= zg <= ZMAX - M )
  G = []( -UMAX <= u <= UMAX )  /\  []( z > ZMAX - M -> u <= 0 )  /\  []( z < M -> u >= 0 )

Delegates:
  planner    (A1, G1):  A1 = []( M <= zg <= ZMAX - M )
                        G1 = []( M <= r <= ZMAX - M )
  controller (A2, G2):  A2 = []( M <= r <= ZMAX - M ) /\ []( 0 <= z <= ZMAX )
                        G2 = []( -UMAX <= u <= UMAX ) /\ []( u * (r - z) >= 0 )

Constraints checked (each is a set inclusion, checked pointwise over the horizon):
  (N1)  A            subset  A1          planner is a source: top assumption establishes its assumption
  (N2)  A /\ G1      subset  A2          controller reads r from the planner and z from the environment
  (Out) A /\ G1 /\ G2 subset G
Each check asks Z3 for a behaviour violating the inclusion; unsat means the inclusion holds.
"""
from z3 import Real, RealVal, And, Or, Not, Implies, Solver, sat, unsat

N = 4
ZMAX, M, UMAX = RealVal(10), RealVal(1), RealVal(2)

z  = [Real(f"z_{t}")  for t in range(N)]
zg = [Real(f"zg_{t}") for t in range(N)]
r  = [Real(f"r_{t}")  for t in range(N)]
u  = [Real(f"u_{t}")  for t in range(N)]

def always(pred):
    return And([pred(t) for t in range(N)])

def contracts(planner_margin=M, env_bounds_z=True):
    A  = And(always(lambda t: And(0 <= z[t], z[t] <= ZMAX)) if env_bounds_z else True,
             always(lambda t: And(M <= zg[t], zg[t] <= ZMAX - M)))
    G  = And(always(lambda t: And(-UMAX <= u[t], u[t] <= UMAX)),
             always(lambda t: Implies(z[t] > ZMAX - M, u[t] <= 0)),
             always(lambda t: Implies(z[t] < M, u[t] >= 0)))
    A1 = always(lambda t: And(M <= zg[t], zg[t] <= ZMAX - M))
    G1 = always(lambda t: And(planner_margin <= r[t], r[t] <= ZMAX - planner_margin))
    A2 = And(always(lambda t: And(M <= r[t], r[t] <= ZMAX - M)),
             always(lambda t: And(0 <= z[t], z[t] <= ZMAX)))
    G2 = And(always(lambda t: And(-UMAX <= u[t], u[t] <= UMAX)),
             always(lambda t: u[t] * (r[t] - z[t]) >= 0))
    return A, G, A1, G1, A2, G2

def inclusion(name, lhs, rhs):
    s = Solver(); s.add(lhs, Not(rhs))
    res = s.check()
    if res == unsat:
        print(f"  {name:4s} holds")
    else:
        m = s.model()
        row = lambda v: [m.eval(x, model_completion=True) for x in v]
        print(f"  {name:4s} FAILS  z={row(z)} r={row(r)} u={row(u)}")
    return res == unsat

def run(title, **kw):
    print(title)
    A, G, A1, G1, A2, G2 = contracts(**kw)
    ok = inclusion("N1", A, A1)
    ok &= inclusion("N2", And(A, G1), A2)
    ok &= inclusion("Out", And(A, G1, G2), G)
    print("  delegation valid" if ok else "  delegation INVALID")
    print()

run("Chosen delegates")
run("Planner band without margin (r may reach the ceiling)", planner_margin=RealVal(0))
run("Query forgets the environment bound on z", env_bounds_z=False)
