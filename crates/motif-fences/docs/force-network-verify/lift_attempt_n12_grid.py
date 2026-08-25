import numpy as np

# vertices, coords
V = {'00':(0,0),'10':(1,0),'20':(2,0),'01':(0,1),'11':(1,1),'21':(2,1),'02':(0,2),'12':(1,2),'22':(2,2)}

# edge stresses (omega_e = 2*lambda_e), from symmetric ansatz solve: a=0.10454545 (boundary), b=0.20909091 (interior)
a = 0.10454545454545  # boundary lambda
b = 0.20909090909091  # interior lambda
c = 0.58181818181818  # active-face pressure (all 4 cells active)

def omega(u,v):
    key = frozenset([u,v])
    boundary_edges = [frozenset(['00','10']), frozenset(['10','20']), frozenset(['00','01']),
                       frozenset(['01','02']), frozenset(['20','21']), frozenset(['21','22']),
                       frozenset(['02','12']), frozenset(['12','22'])]
    interior_edges = [frozenset(['10','11']), frozenset(['01','11']), frozenset(['11','21']), frozenset(['11','12'])]
    if key in boundary_edges: return 2*a
    if key in interior_edges: return 2*b
    raise KeyError((u,v))

# faces as ordered vertex lists CCW, plus 'outer' (CW when viewed as bounded-complement, use CCW of the boundary reversed)
faces = {
  'cell00': ['00','10','11','01'],
  'cell10': ['10','20','21','11'],
  'cell01': ['01','11','12','02'],
  'cell11': ['11','21','22','12'],
  'outer':  ['00','01','02','12','22','21','20','10'],  # CCW when outer face traversed with interior on right -> equivalent to CW of the square; check orientation below
}

def signed_area(poly):
    s=0.0
    n=len(poly)
    for i in range(n):
        x1,y1=V[poly[i]]; x2,y2=V[poly[(i+1)%n]]
        s+=x1*y2-x2*y1
    return s/2

for name,poly in faces.items():
    print(name, "signed area", signed_area(poly))

# keep outer as originally listed (CW = correct interior-on-left convention for unbounded face)
print("outer reversed area:", signed_area(faces['outer']))

def R90(v):
    x,y = v
    return (-y, x)

edge_owner = {}  # (u,v) directed -> face name
for name, poly in faces.items():
    n = len(poly)
    for i in range(n):
        u,v = poly[i], poly[(i+1)%n]
        edge_owner[(u,v)] = name

# build undirected edge list with both owners
und_edges = set()
for (u,v) in edge_owner:
    key = frozenset([u,v])
    und_edges.add(key)

edges_info = []
for key in und_edges:
    u,v = tuple(key)
    if (u,v) in edge_owner:
        f_fwd = edge_owner[(u,v)]
        f_bwd = edge_owner[(v,u)]
        edges_info.append((u,v,f_fwd,f_bwd))
    else:
        u,v = v,u
        f_fwd = edge_owner[(u,v)]
        f_bwd = edge_owner[(v,u)]
        edges_info.append((u,v,f_fwd,f_bwd))

# BFS to assign slope s_F for every face using s_F_fwd - s_F_bwd = omega(u,v)*R90(v-u)
import collections
adj = collections.defaultdict(list)
for (u,v,ff,fb) in edges_info:
    w = omega(u,v)
    dvu = (V[v][0]-V[u][0], V[v][1]-V[u][1])
    rhs = R90(dvu)
    rhs = (w*rhs[0], w*rhs[1])
    adj[ff].append((fb, (-rhs[0],-rhs[1])))  # s_fb = s_ff - rhs  => s_fb - s_ff = -rhs
    adj[fb].append((ff, rhs))                 # s_ff = s_fb + rhs

s = {'outer': (0.0,0.0)}
Q = collections.deque(['outer'])
visited = {'outer'}
while Q:
    f = Q.popleft()
    for (g, delta) in adj[f]:
        if g not in visited:
            s[g] = (s[f][0]+delta[0], s[f][1]+delta[1])
            visited.add(g)
            Q.append(g)

print("slopes s_F:")
for f,v in s.items():
    print(" ", f, v)

# now integrate heights: h_F(x,y) = s_F . (x,y) + c_F
# pick one vertex, say '00', set global height 0 via outer face (since '00' is on outer boundary)
c = {}
c['outer'] = 0.0 - (s['outer'][0]*V['00'][0] + s['outer'][1]*V['00'][1])
visited2 = {'outer'}
Q = collections.deque(['outer'])
while Q:
    f = Q.popleft()
    for (g, _delta) in adj[f]:
        if g not in visited2:
            # find a shared vertex between f and g to match heights
            polyf = faces[f]; polyg = faces[g]
            shared = set(polyf) & set(polyg)
            vtx = next(iter(shared))
            x,y = V[vtx]
            h_here = s[f][0]*x+s[f][1]*y+c[f]
            c[g] = h_here - (s[g][0]*x + s[g][1]*y)
            visited2.add(g)
            Q.append(g)

print("c_F:", c)

print("\nheight consistency check per vertex:")
for vtx, (x,y) in V.items():
    vals = []
    for f, poly in faces.items():
        if vtx in poly:
            h = s[f][0]*x+s[f][1]*y+c[f]
            vals.append((f,h))
    hs = [h for _,h in vals]
    print(f"  {vtx}: {vals}  spread={max(hs)-min(hs):.6f}")
