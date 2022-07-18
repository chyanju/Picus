import re

from igraph import *
from itertools import product
from functools import reduce

def gen_dg(r1cs_txt):
    with open(r1cs_txt, "r") as f:
        r1cs_constraints = f.readlines()
    print(r1cs_constraints[-4])
    print(r1cs_constraints[-3])
    # collect all dependencies
    depsL = []
    depsR = []
    for p in r1cs_constraints[1:-4]:
        pl, pr = p.split("=")
        pattern0 = re.compile(r"(x.*?)\)")
        depsL.append(pattern0.findall(pl))
        depsR.append(pattern0.findall(pr))

    # parse all pts
    depsL = [[int(x.replace("x","")) for x in p] for p in depsL]
    depsR = [[int(x.replace("x","")) for x in p] for p in depsR]
    # collect all points with deps
    pts = set(reduce(lambda x,y: x+y, depsL, []) + reduce(lambda x,y: x+y, depsR, []))
    print("# collected vertices: {}".format(len(pts)))
    
    print("# constructing graph...")
    g = Graph()
    g.add_vertices(len(pts))

    for p in depsR:
        q = list(product(p, p))
        g.add_edges(q)
    for p in depsL:
        q = list(product(p, p))
        g.add_edges(q)
        
    return g

g = gen_dg("../benchmarks/ecne/Poseidon@poseidon.r1cs.log")
print("# plotting...")
for p in g.vs:
    p["label_size"]=5
    visual_style = {}
    visual_style["margin"]=40
    visual_style["bbox"]=(600,400)
    visual_style["vertex_size"]=1
plot(g, **visual_style)