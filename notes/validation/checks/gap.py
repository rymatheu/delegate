# Shape gap of an isotropic tube vs an inward corner-cutting path.
# Path: p0 -> w1 -> w2 with the corner at w1 replaced by a circular arc tangent to both legs,
# starting at blend distance L before w1. rho_min = max distance from path to polyline.
# Fence facet normal n = (0,-1) (bottom side y >= -s); w1 is the lowest vertex.
import numpy as np
def seg_dist(z,a,b):
    ab=b-a; t=np.clip(np.dot(z-a,ab)/np.dot(ab,ab),0,1); return np.linalg.norm(z-(a+t*ab))
def run(L, p0, w1, w2, n=np.array([0.,-1.])):
    u1=(w1-p0)/np.linalg.norm(w1-p0); u2=(w2-w1)/np.linalg.norm(w2-w1)
    a=w1-L*u1; b=w1+L*u2                      # tangent points
    th=np.arccos(np.clip(np.dot(u1,u2),-1,1))  # turn angle
    r=L/np.tan(th/2)                           # arc radius
    # centre: from a, perpendicular to u1 towards the turn
    perp=np.array([-u1[1],u1[0]]); 
    if np.dot(perp,u2)<0: perp=-perp
    c=a+r*perp
    angs=np.linspace(0,1,4001)
    v0=a-c; v1=b-c
    phi0=np.arctan2(v0[1],v0[0]); phi1=np.arctan2(v1[1],v1[0])
    dphi=(phi1-phi0+np.pi)%(2*np.pi)-np.pi
    arc=np.array([c+r*np.array([np.cos(phi0+s*dphi),np.sin(phi0+s*dphi)]) for s in angs])
    path=np.vstack([np.linspace(p0,a,500),arc,np.linspace(b,w2,500)])
    rho_min=max(min(seg_dist(z,p0,w1),seg_dist(z,w1,w2)) for z in path)
    sig_D=max(path@n); sig_poly=max(np.array([p0,w1,w2])@n)
    return rho_min, sig_poly-sig_D
p0=np.array([-30.,0.]); w1=np.array([0.,-40.]); w2=np.array([30.,0.])
for L in [1,2,4,8]:
    rm,cut=run(L,p0,w1,w2)
    print(f"blend L={L}: rho_min={rm:.3f}, cut depth in facet direction={cut:.3f}, "
          f"margin G1 demands at rho=rho_min: {rm:.3f}, exact needs: {-cut:.3f}, gap={rm+cut:.3f}")
