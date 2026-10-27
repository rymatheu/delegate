# Random finite models: ports U,W,E,Y with 2-3 values each. Checks, by enumeration:
# (1) planner implements (A1,G1) iff it implements the AG quotient (Pacti/Incer closed form);
# (2) G1 subset V cap G1x when M2 certified; (3) Bad empty iff a total planner exists;
# (4) the 'Hence' reading holds under 'every (u,e) admits a y outside G' and can fail without it.
import itertools, random
random.seed(11)
def rs(*dims, p=.6): return {x for x in itertools.product(*[range(d) for d in dims]) if random.random()<p}
fails={1:0,2:0,3:0,4:0}; hence_fail_without=0; N=3000
for _ in range(N):
    nu,nw,ne,ny=[random.randint(1,3) for _ in range(4)]
    A=rs(nu,ne); G=rs(nu,ne,ny,p=.7); V={w for w in range(nw) if random.random()<.7}
    P=rs(nw,ne,p=.7); T=rs(nw,ne,ny,p=.5)
    G2=lambda w,e,y: ((w,e) not in P) or ((w,e,y) in T)
    A1={u for u in range(nu) if any((u,e) in A for e in range(ne))}
    G1={(u,w) for u in range(nu) for w in range(nw) if w in V and all(((u,e) not in A) or (not G2(w,e,y)) or ((u,e,y) in G) for e in range(ne) for y in range(ny))}
    # (1) over all planners (relations) -- sample some
    for _ in range(5):
        M1=rs(nu,nw,p=.5)
        imp1=all((u not in A1) or ((u,w) in G1) for (u,w) in M1)
        Aq=lambda u,w,e,y: ((u,e) in A) and (G2(w,e,y) or w not in V)
        Gq=lambda u,w,e,y: (w in V and (u,e,y) in G) or not Aq(u,w,e,y)
        imp2=all((not Aq(u,w,e,y)) or Gq(u,w,e,y) for (u,w) in M1 for e in range(ne) for y in range(ny))
        fails[1]+= imp1!=imp2
    # (2) M2 certified: any subset of V x P -> T plus arbitrary outside
    M2={(w,e,y) for w in range(nw) for e in range(ne) for y in range(ny) if (w not in V or (w,e) not in P or (w,e,y) in T) and random.random()<.6}
    G1x={(u,w) for u in range(nu) for w in range(nw) if all(((u,e) not in A) or ((w,e,y) not in M2) or ((u,e,y) in G) for e in range(ne) for y in range(ny))}
    fails[2]+= not all((w in V) and (u,w) in G1x for (u,w) in G1)
    # (3)
    bad_empty = all(any((u,w) in G1 for w in range(nw)) for u in A1)
    total_exists = all(any(((u,w) in G1) or (u not in A1) for w in range(nw)) for u in range(nu))
    fails[3]+= bad_empty!=total_exists
    # (4) Hence: G1 nonempty iff exists u,w in V with A(u,.) sub P(w,.) and A cap T sub G at (u,w)
    reading = any(w in V and all(((u,e) not in A) or (w,e) in P for e in range(ne)) and all(((u,e) not in A) or ((w,e,y) not in T) or (u,e,y) in G for e in range(ne) for y in range(ny)) for u in range(nu) for w in range(nw))
    hyp = all(any((u,e,y) not in G for y in range(ny)) for (u,e) in A)
    if hyp: fails[4]+= (len(G1)>0)!=reading
    else: hence_fail_without += (len(G1)>0)!=reading
print('disagreements:', fails, '| Hence reading wrong when hypothesis fails:', hence_fail_without, 'of', N)
