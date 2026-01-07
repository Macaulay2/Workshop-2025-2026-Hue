newPackage(
    "3RegularGraphs",
    Version => "0.1",
    Date => "",
    Headline => "",
    Authors => {{ Name => "", Email => "", HomePage => ""}},
    PackageImports => {Nauty, EdgeIdeals},
    Keywords => {""},
    AuxiliaryFiles => false,
    DebuggingMode => false
    )

export {alpha}
-* Code section *-

alpha = method(Options => {OnlyBiconnected => true})
alpha Ideal := o -> JG -> (
    --- !! assumes input is Alexander dual of edge ideal!!
    numEdges := degree JG;
    iJG := min \\ first \ degree \ JG_*;
    cG := codim JG;
    numEdges / (iJG)^cG
    )
alpha ZZ := o -> n -> (
    R := QQ[x_0..x_(n-1)];
    listOfGraphs := generateGraphs(R, OnlyBiconnected => o.OnlyBiconnected); -- todo:
    min \\ alpha \ dual \ edgeIdeal \ listOfGraphs
    )
    

-* Documentation section *-
beginDocumentation()

doc ///
Key
3RegularGraphs

Headline
Description
Text
Tree
Example
CannedExample
Acknowledgement
Contributors
References
Caveat
SeeAlso
Subnodes
///

doc ///
Key
Headline
Usage
Inputs
Outputs
Consequences
Item
Description
Text
Example
CannedExample
Code
Pre
ExampleFiles
Contributors
References
Caveat
SeeAlso
///

-* Test section *-
TEST /// -* [insert short title for this test] *-
-- test code and assertions here
-- may have as many TEST sections as needed
///

end--

-* Development section *-
restart
path = append(path, "./")
debug needsPackage "3RegularGraphs"
"
check "3RegularGraphs
"

uninstallPackage "3RegularGraphs"
restart
installPackage "3RegularGraphs"
viewHelp "3RegularGraphs



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


