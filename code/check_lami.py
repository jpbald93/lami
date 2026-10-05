import math, random
def norm(v): return math.hypot(*v)
def cross(u,v): return u[0]*v[1]-u[1]*v[0]
def dot(u,v): return u[0]*v[0]+u[1]*v[1]
def oangle(u,v): return math.atan2(cross(u,v), dot(u,v))
def angle(u,v): return math.acos(max(-1,min(1,dot(u,v)/(norm(u)*norm(v)))))
random.seed(1); worst=0
for _ in range(100000):
    F1=(random.uniform(-5,5),random.uniform(-5,5)); F2=(random.uniform(-5,5),random.uniform(-5,5))
    F3=(-F1[0]-F2[0],-F1[1]-F2[1])
    if min(map(norm,(F1,F2,F3)))<1e-3: continue
    a=[norm(F2)*norm(F3)*math.sin(oangle(F2,F3)), norm(F3)*norm(F1)*math.sin(oangle(F3,F1)), norm(F1)*norm(F2)*math.sin(oangle(F1,F2))]
    b=[norm(F2)*norm(F3)*math.sin(angle(F2,F3)), norm(F3)*norm(F1)*math.sin(angle(F3,F1)), norm(F1)*norm(F2)*math.sin(angle(F1,F2))]
    worst=max(worst,max(a)-min(a),max(b)-min(b))
    s=[math.sin(angle(F2,F3)),math.sin(angle(F3,F1)),math.sin(angle(F1,F2))]
    if min(s)>1e-3:
        r=[norm(F1)/s[0],norm(F2)/s[1],norm(F3)/s[2]]; worst=max(worst,(max(r)-min(r))/max(r))
    # angle sum: unoriented angles of three equilibrium forces sum to 2π
    worst=max(worst,abs(angle(F2,F3)+angle(F3,F1)+angle(F1,F2)-2*math.pi) if min(s)>1e-3 else 0)
print("max discrepancy", worst); assert worst<1e-6
# degenerate collinear case: F1=(1,0),F2=(2,0),F3=(-3,0): all sines zero
F1,F2,F3=(1,0),(2,0),(-3,0)
print([math.sin(angle(*p)) for p in ((F2,F3),(F3,F1),(F1,F2))]); print("OK")
