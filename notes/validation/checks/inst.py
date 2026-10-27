# Worked-example instance s=50, h=(-40,-40), g=(40,40), mission ((0,-49),(40,40)).
# Toy controller: target follows the polyline p0->w1->w2 with the corner at w1 replaced by an inward
# circular arc tangent to both legs, blend length L. Exact quotient (fence part) needs every target in
# F_50 for every start p0 with |p0-h|<=1; G1 needs the rho=2 tube inside F_50.
import numpy as np
def path(p0,w1,w2,L,n=400):
    u1=(w1-p0)/np.linalg.norm(w1-p0); u2=(w2-w1)/np.linalg.norm(w2-w1)
    a=w1-L*u1; b=w1+L*u2
    th=np.arccos(np.clip(u1@u2,-1,1)); r=L/np.tan(th/2)
    perp=np.array([-u1[1],u1[0]]); perp = perp if perp@u2>0 else -perp
    c=a+r*perp; v0=a-c; v1=b-c
    f0=np.arctan2(v0[1],v0[0]); f1=np.arctan2(v1[1],v1[0]); df=(f1-f0+np.pi)%(2*np.pi)-np.pi
    arc=np.array([c+r*np.array([np.cos(f0+t*df),np.sin(f0+t*df)]) for t in np.linspace(0,1,n)])
    return np.vstack([np.linspace(p0,a,n),arc,np.linspace(b,w2,n)])
def segd(z,a,b):
    ab=b-a; t=np.clip((z-a)@ab/(ab@ab),0,1); return np.linalg.norm(z-(a+t*ab))
h=np.array([-40.,-40.]); w1=np.array([0.,-49.]); w2=np.array([40.,40.]); s=50
for L in [0.5,1,2,3]:
    worst=-1e9; rmin=0
    for ang in np.linspace(0,2*np.pi,73):
        p0=h+np.array([np.cos(ang),np.sin(ang)])
        P=path(p0,w1,w2,L)
        worst=max(worst,np.max(np.abs(P)))
        rmin=max(rmin,max(min(segd(z,p0,w1),segd(z,w1,w2)) for z in P[::10]))
    print(f"L={L}: max |target|_inf over starts = {worst:.3f} (fence {s}); deviation rho_min ~ {rmin:.3f}; "
          f"exact quotient accepts: {worst<=s}; G1 with rho=2 accepts: {max(abs(w1).max(),abs(w2).max())<=s-2}")
