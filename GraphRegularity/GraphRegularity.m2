newPackage(
    "GraphRegularity",
    Version => "0.1",
    Date => "",
    Headline => "",
    Authors => {{ Name => "", Email => "", HomePage => ""}},
    PackageExports => {"Nauty", "EdgeIdeals"},
    Keywords => {""},
    AuxiliaryFiles => false,
    DebuggingMode => false
    )

export {"alpha", "Reg", "isBiconnected"}
-* Code section *-

regularity Graph := o -> G -> regularity edgeIdeal G

alpha = method(Options => {OnlyBiconnected => false, MinDegree => 1, MaxDegree => null, Reg => null})
alpha Graph := o -> G -> (
    JG := dual edgeIdeal G;
    alpha(JG, o)
    )
alpha Ideal := o -> JG -> (
    --- !! assumes input is Alexander dual of edge ideal!!
    numEdges := degree JG;
    iJG := min \\ first \ degree \ JG_*;
    cG := codim JG;
    numEdges / (iJG)^cG
    )
alpha ZZ := o -> n -> (
    noReg := instance(o.Reg, Nothing);
    assert(noReg or instance(o.Reg, ZZ));
    R := QQ[vars(0..n-1)];
    listOfGraphs := generateGraphs(R, OnlyBiconnected => o.OnlyBiconnected, MinDegree => o.MinDegree, MaxDegree => o.MaxDegree); -- todo:
    if not noReg then listOfGraphs = select(listOfGraphs, G -> regularity G == o.Reg);
    min apply(dual \ edgeIdeal \ listOfGraphs, JG -> alpha(JG, o))
    )


isBiconnected = method()
isBiconnected Graph := G -> (
    V := vertices G;
    isConnected G and all(V, v -> isConnected inducedGraph(G, delete(v, vertices G)))
    )

-* Documentation section *-
beginDocumentation()

doc ///
Key
  GraphRegularity
Headline
  A cook package
Description
  Text
    hello
///

-* Test section *-

TEST ///
-- test for 5-vertex graphs
assert(alpha 5 == 4/9)
assert(alpha(5, OnlyBiconnected=>true) == 5/9)
///

TEST ///
-- test for biconnectivity
R = QQ[x_0..x_2]
assert(not isBiconnected graph ideal(x_0*x_1, x_1*x_2))
assert(not isBiconnected graph ideal(x_0*x_1))
assert(isBiconnected graph ideal(x_0*x_1, x_1*x_2, x_0*x_2))
///


end--

-* Development section *-
restart
path = append(path, "./")
needsPackage "GraphRegularity"
check "GraphRegularity"
R = QQ[x_0..x_8]
grs = generateRandomGraphs(R, 100, .5);
goodGraphs = select(grs, G -> isBiconnected G and regularity G == 3);
min \\ alpha \ goodGraphs
select(goodGraphs, G -> alpha G == 4/9)


uninstallPackage "GraphRegularity"
restart
installPackage "GraphRegularity"
viewHelp "GraphRegularity"

needsPackage "Nauty"
n = 9
R = QQ[x_0..x_(n-1)]
conjecturedMinimumAlpha = n -> (
    local m;
    if n%2 == 0 then (
	m = sub(n/2, ZZ);
	(m^2 - m)/(4*m^2 - 8*m + 4)
	) else (
	m = sub((n+1)/2, ZZ);
	((m-1)/(2*m-3))^2
	)
    )
elapsedTime grs = filterGraphs(removeIsomorphs generateRandomGraphs(R, 100000, .5), buildGraphFilter {"Connectivity" => 0, "NegateConnectivity" => true, "MinDegree" => 1});
elapsedTime reg3Graphs = select(grs, G -> regularity G == 3);
elapsedTime a0 = min \\ alpha \ reg3Graphs
champions = select(reg3Graphs, G -> alpha G == a0);
# champions
regularity \ champions 
netList champions



restart
needsPackage "Nauty"
needsPackage "EdgeIdeals"
n = 14
R = QQ[x_0..x_(n-1)]
k = sub(n/2, ZZ)
G1 = completeGraph take(gens R, k)
G2 = completeGraph drop(gens R, n-k)
IG = edgeIdeal G1 + edgeIdeal G2
JG = dual IG
makeAlexanderDual = IG -> ideal dual simplicialComplex IG

JG1 = makeAlexanderDual edgeIdeal G1
JG2 = makeAlexanderDual edgeIdeal G2
netList decompose(JG1+JG2)



n = 7
R = QQ[x_0..x_(n-1)]




-- one of two "champions" for 6-vertex, biconnected, 3-regular graphs
n=6
R = QQ[x_0..x_5]
G = graph {{0,1}, {0,2}, {1,2}, {3,4}, {3,5}, {4,5}, {0,3}, {2,5}}
IG = makeEdgeIdeal G
vertexConnectivity G >= 2
regularity IG >= 3
JG = makeAlexanderDual G
7/(2*(n+1))
alpha JG



n = 7
R = QQ[x_0..x_(n-1)]
elapsedTime listOfGraphs = drop(generateGraphs(R, OnlyBiconnected=>true), -1);
complement Graph := G -> graph \\ product \ toList(set edges completeGraph G#"ring" - set edges G)
complement \ listOfGraphs

makeEdgeIdeal = G -> sub(ideal \\ product \ edges G, R)
makeAlexanderDual = G -> intersection apply(edges G, e -> ideal e)
makeAlexanderDual2 = G -> ideal dual simplicialComplex makeE
initialDegree = I -> min \\ first \ degree \ I_*
reg = I -> regularity I
-- omit complete and empty graphs



-- Q2
P = partition(G -> (regularity makeEdgeIdeal G == 3), listOfGraphs) ;
length(P#true), length(P#false)
elapsedTime apply(P#true, G -> (
	JG := makeAlexanderDual G;
	c := codim JG;
	iJ := initialDegree JG;
	(length edges G)/iJ^c
	)
    )
min oo


