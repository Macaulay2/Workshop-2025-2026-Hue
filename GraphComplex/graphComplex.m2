restart
needsPackage "Graphs";

--path graph
d = 3 --number of edges (d+1 vertices)
G = graph for i from 0 to d-1 list {i,i+1}
E = edges G 
V = vertexSet G
W = hashTable for i in V list i => 1 --weights of vertices of G

deleteEdges(G,{{2,1}})

subsets(5,3)

p = 3; kk = ZZ/p
C = for i from 0 to d list directSum(apply(subsets(d,i),s -> s => kk^1))
components(C#1)
indices(C#1)

(C#1)_[{0}]
(C#2)^[{0,1}]

--
E
subGraph = (G,J) -> graph for e in J list E#e
subGraph(G,{1})

weightGraph = GJ -> (
    sum for v in vertexSet GJ list W#v
    )
weightGraph subGraph(G,{})


--want to generate differentials in C_*
for i from 1 to d list (
    sum flatten for J in indices(C#i) list
    (
	GJ := subGraph(G,J);
	for j from 0 to i-1 list
	(
	    ej := toList E#(J#j);
	    v1 := ej#0;
	    w := sum for v in GJ#v1 list W#v;
	    G1 := deleteEdges(GJ,ej);
	    w1 := sum for v in G1#v1 list W#v;
	    (-1)^j * binomial(w,w1) * (C#(i-1))_[drop(J,{j,j})] * (C#i)^[J]
	    )
	)
    )



restart
needsPackage "Graphs";
needsPackage "Matroids";

-- build a simple graph from an edge list
G = graph({{w,x},{w,y},{w,z},{y,z}});  -- vertices can be symbols

M = matroid G;                 -- graphic matroid
Delta = independenceComplex M; -- faces = forests
Delta
