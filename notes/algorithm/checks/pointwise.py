# brute-force check of the pointwise lemma on finite tick domains
import itertools, random
random.seed(3)
Z = range(4)
def rnd(): return frozenset(z for z in Z if random.random() < .5)
bad = 0; trials = 0
for _ in range(4000):
    H = random.randint(0, 3); m = random.randint(0, 2)
    al = rnd(); gs = [rnd() for _ in range(m)]; c = rnd(); d = rnd()
    G = [frozenset(Z)] + gs          # gamma_0 = true
    sigs = list(itertools.product(Z, repeat=H+1))
    ant = lambda s: all(z in al for z in s) and all(any(z in g for z in s) for g in gs)
    box = all((not ant(s)) or all(z in c for z in s) for s in sigs)
    dia = all((not ant(s)) or any(z in d for z in s) for s in sigs)
    pbox = any(not (al & g) for g in G) or al <= c
    pdia = any((al & g) <= d for g in G)
    if H + 1 >= m + 1:   # condition of the lemma (H >= m)
        trials += 1
        bad += (box != pbox) + (dia != pdia)
print('cases with H>=m:', trials, 'disagreements:', bad)
