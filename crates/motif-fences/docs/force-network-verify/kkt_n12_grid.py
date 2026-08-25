import numpy as np

# 3x3 lattice of vertices for a 2x2 grid of unit cells
names = [f'v{x}{y}' for y in range(3) for x in range(3)]
idx = {n:i for i,n in enumerate(names)}
def vn(x,y): return f'v{x}{y}'
coords = {vn(x,y):(float(x),float(y)) for x in range(3) for y in range(3)}
x0 = np.array([coords[n] for n in names]).reshape(-1)

def P(x,n):
    i=idx[n]; return x[2*i:2*i+2]

def shoelace(pts):
    a=0.0; n=len(pts)
    for i in range(n):
        x1,y1=pts[i]; x2,y2=pts[(i+1)%n]
        a += x1*y2-x2*y1
    return a/2.0

fences=[]
labels_f=[]
for y in range(3):
    for x in range(2):
        fences.append((vn(x,y), vn(x+1,y)))
for x in range(3):
    for y in range(2):
        fences.append((vn(x,y), vn(x,y+1)))

faces = {}
for x in range(2):
    for y in range(2):
        faces[f'cell{x}{y}'] = [vn(x,y), vn(x+1,y), vn(x+1,y+1), vn(x,y+1)]

outer = [vn(0,0), vn(1,0), vn(2,0), vn(2,1), vn(2,2), vn(1,2), vn(0,2), vn(0,1)]

def numgrad(f,x,eps=1e-7):
    g=np.zeros_like(x)
    for i in range(len(x)):
        xp=x.copy(); xp[i]+=eps
        xm=x.copy(); xm[i]-=eps
        g[i]=(f(xp)-f(xm))/(2*eps)
    return g

x=x0.copy()
rows=[]; labels=[]
for (u,v) in fences:
    g=numgrad(lambda xx,u=u,v=v: np.dot(P(xx,u)-P(xx,v),P(xx,u)-P(xx,v))-1.0, x)
    rows.append(g); labels.append(f'len_{u}_{v}')

areas = {k: abs(shoelace([P(x,n) for n in v])) for k,v in faces.items()}
print("face areas:", areas)
active = list(faces.keys())  # all active
for k in active:
    g=numgrad(lambda xx,k=k: abs(shoelace([P(xx,n) for n in faces[k]])), x)
    rows.append(g); labels.append(f'area_{k}')

J=np.array(rows)
gradA = numgrad(lambda xx: abs(shoelace([P(xx,n) for n in outer])), x)
v,res,rank,sv = np.linalg.lstsq(J.T, gradA, rcond=None)
resid = J.T@v - gradA
print("rank J.T:", rank, "shape:", J.shape, "ncols:", J.shape[1])
print("residual norm:", np.linalg.norm(resid))
for lab,val in zip(labels,v):
    print(f"  {lab}: {val:.6f}")

print("\n--- nullspace of J.T (self-stress space, zero load) ---")
U,S,Vt = np.linalg.svd(J.T)
tol = 1e-6
null_mask = S < tol if len(S)==J.T.shape[1] else None
# J.T is 18x16; nullspace of J.T (as a map from R^16 -> R^18) is vectors w in R^16 with J.T @ w = 0
# svd of J.T (18x16): null space of the matrix (right null vectors) corresponds to V columns with singular value ~0, dimension 16 - rank
Ufull,Sfull,Vtfull = np.linalg.svd(J.T, full_matrices=True)
rank = np.sum(Sfull>1e-8)
print("singular values:", Sfull)
nullspace = Vtfull[rank:,:]  # rows spanning null space, in R^16
print("nullspace dim:", nullspace.shape[0])
for i,row in enumerate(nullspace):
    print(f"null vec {i}:")
    for lab,val in zip(labels,row):
        if abs(val)>1e-6:
            print(f"    {lab}: {val:.4f}")

print("\n--- symmetric ansatz check ---")
boundary_idx = [0,1,4,5,6,7,10,11]
interior_idx = [2,3,8,9]
area_idx = [12,13,14,15]
Jsym = np.zeros((J.shape[0], 3))
Jsym[:,0] = J[boundary_idx,:].sum(axis=0) @ np.eye(J.shape[1])  # wrong, fix below
