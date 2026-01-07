newPackage(
"WeightedGraphComplex",
         Version => "0.1",
         Date => "January 7, 2026",
         Headline => "Weighted Independence Complex of Graph",
         Authors => {{ Name => "Me", Email => "", HomePage => ""}},
         Keywords => {""},
         AuxiliaryFiles => false,
         DebuggingMode => false,
	 PackageExports => {"Complexes", "Graphs"}
         )

     export {--"connectedComponent",
	    -- "weightGraph",
	     "makeGComplex",
	     "homologyRanksGComplex"}

     -* Code section *-

connectedComponent = (G,v) -> flatten breadthFirstSearch(G,v)
weightGraph = (w,S) -> sum for i in S list w#i

makeGComplex = method()
makeGComplex (Graph,HashTable,List) := (G,w,ringEls) -> (
    R := ring ringEls#0;
    E := edges G; --edge set of E
    d := length E; --number of edges
    lenC := length(vertexSet G) - (numberOfComponents G); --length of the complex
    L := for i from 0 to lenC list
             select(subsets(d,i),A -> isForest graph apply(A,x->E#x)); --list of forests in G
    C := for i from 0 to lenC list --the terms in the complex
             directSum(for s in L#i list s=> R^1);
    difsC := for i from 1 to lenC list ( --the differentials in the complex
        sum flatten for A in indices(C#i) list(
	    P1 := (C#i)^[A] ;
	    GA := graph apply(A,x->E#x);
	    for j from 0 to i-1 list(
	        Ej := toList E#(A#j);
		vj := Ej#0;
	        wj := weightGraph(w,connectedComponent(GA,vj));
		B := drop(A,{j,j});
		GB := deleteEdges(GA,{Ej});
	        wbj := weightGraph(w,connectedComponent(GB,vj));
        	ringEls#(A#j)*binomial(wj,wbj)*(-1)^j*(C#(i-1))_[B] * (C#i)^[A]
	    )
	)
    );
    complex difsC
)


makeGComplex (Graph,HashTable,Ring) := (G,w,R) -> makeGComplex(G,w,splice{#(edges G):1_R})




homologyRanksGComplex = method()
homologyRanksGComplex (Graph,HashTable,Ring) := (G,w,K) -> (
    C := makeGComplex(G,w,K);
    (a,b) := C.concentration;
    new HashTable from for i from a to b list i => rank HH_i C
    )


     -* Documentation section *-
     beginDocumentation()
     emacs
     doc ///
     Key
       WeightedGraphComplex
     Headline
       Weighted independence complex of a graph
     Description
       Text
         This package creates a weighted version of the
	 independence complex of the graphical matroid
	 associated to some graph G.
     ///
     
     doc ///
     Key
       makeGComplex
     Headline
       Weighted independence complex of a graph
     Usage
       makeGComplex(G,w,ringEls)
       makeGComplex(G,w,R)
     Inputs
       G:Graph
         a graph whose independence complex is to be computed
       w:HashTable
         describes weights of the vertices of G
       ringEls:List
         a list of ring elements, one for each edge of G
       R:Ring
         the ring over which the complex is computed
     Outputs
       :Complex
         Weighted independence complex of the graph G
     Description
       Text
         Creates a weighted version of independence complex of the graphical matroid
	 associated to graph G. By default each edge is assigned the unit element of the
	 ring R.
	 Below we show an example with G a path graph and R the ring of integers
       Example
	 G = graph({{a,b},{b,c},{c,d}})
	 w = new HashTable from {a => 1, b => 2, c => 3, d => 4}
	 C = makeGComplex(G,w,ZZ)
	 C.dd
	 prune(HH_1 C)
	 prune(HH_3 C)
       Text
         We perform the same calculation over the field with 5 elements and G as before.
       Example
	 C1 = makeGComplex(G,w,ZZ/5)
	 C1.dd
	 prune(HH_1 C1)
	 prune(HH_3 C1)
       Text
         More generally, we can assign to each edge an element of the ring and construct
	 a weighted complex with parameters given by these elements.
       Example
         R = ZZ/2[t]
	 ringEls = {t,t^2,t^3}
	 C2 = makeGComplex(G,w,ringEls)
	 C2.dd
	 prune(HH_1 C2)
	 prune(HH_3 C2)
     ///

     doc ///
     Key
       homologyRanksGComplex
     Headline
       Homology ranks for weighted independence complex of a graph
     Usage
       homologyRanksGComplex(G,w,K)
     Inputs
       G:Graph
         a graph whose homology ranks of the independence complex are to be computed
       w:HashTable
         describes weights of the vertices of G
       K:Ring
         a field over which the complex is computed
     Outputs
       :Complex
         weighted independence complex of the graph G
     Description
       Text
         We compute the ranks for a 4-cycle graph with all vertices having weight 1.
       Example
         G = graph({{a,b},{b,c},{c,d},{a,d}})
	 w = new HashTable from {a => 1, b => 1, c => 1, d => 1}
	 L = for K in {QQ,ZZ/2,ZZ/3,ZZ/5,ZZ/7,ZZ/11} list {K, homologyRanksGComplex(G,w,K)};
	 netList L
     ///
     
     
     end
     -* Test section *-
     TEST /// -* [insert short title for this test] *-
     -- test code and assertions here
     -- may have as many TEST sections as needed
     ///

     end--

     -* Development section *-
     restart

     debug needsPackage "WeightedGraphComplex"
     check "WeightedGraphComplex"

     uninstallPackage "WeightedGraphComplex"
     restart
     prefixPath = {"~/Desktop"} | prefixPath
     installPackage "WeightedGraphComplex"
     viewHelp "WeightedGraphComplex"


