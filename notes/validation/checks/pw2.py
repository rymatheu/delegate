# Separate the side conditions of the Box and Diamond halves of the pointwise lemma.
import itertools, random
random.seed(7)
Z = range(4)
def rnd(): return frozenset(z for z in Z if random.random() < .5)
stats = {}
for _ in range(6000):
    H = random.randint(0, 3); m = random.randint(0, 3)
    al = rnd(); gs = [rnd() for _ in range(m)]; c = rnd(); d = rnd()
    sigs = list(itertools.product(Z, repeat=H+1))
    ant = lambda s: all(z in al for z in s) and all(any(z in g for z in s) for g in gs)
    box = all((not ant(s)) or all(z in c for z in s) for s in sigs)
    dia = all((not ant(s)) or any(z in d for z in s) for s in sigs)
    pbox = (not al) or any(not (al & g) for g in gs) or al <= c
    pdia = al <= d or any((al & g) <= d for g in gs)
    for name, ok, cond in (('box H>=m', box == pbox, H >= m), ('box H<m', box == pbox, H < m),
                           ('dia H+1>=m', dia == pdia, H + 1 >= m), ('dia H+1<m', dia == pdia, H + 1 < m)):
        if cond:
            t = stats.setdefault(name, [0, 0]); t[0] += 1; t[1] += (not ok)
for k, (n, bad) in sorted(stats.items()): print(f'{k}: cases {n}, disagreements {bad}')
