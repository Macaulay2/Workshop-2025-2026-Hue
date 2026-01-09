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

-- Question about the ratio of degree and (initial degree)^(codimension)

-- 1. Introduction to the question
-* 
Given a hypergraph G, let I be the edge ideal in S = QQ[x_1..x_n] of G.
Let J be the ideal of "Alexander dual" of Stanley-Reisner complex of I(G).

Fact: If S/J is Cohen-Macaulay, then i(J)^(e) ≤ (e!)d where d = degree(S/I) and e = codim(I). 

Here, if G is a graph (without isolated vertex), then for J,
    1. codim(J) = 2
    2. degree(S/J) = |E(G)|
    3. i(J) = minimum of size of vertex cover of G.

Question: Suppose G is a graph such that reg(I(G)) ≤ 3. 
Then can we find a constant c for this class of graphs such that ci(J)^e ≤ d?  
*-

-- Presets
needsPackage "Visualize"
needsPackage "Nauty"
needsPackage "EdgeIdeals"

-- Codes
makeDualIdeal = G -> dual \\ edgeIdeal G
-- We checked that it is faster than taking intersection of ideals(x_i,x_j)
initialDegree = I -> min \\ first \ degree \ I_*
reg = I -> regularity I
alphaValue = G -> (
       JG := makeDualIdeal G;
       (length edges G)/((initialDegree JG)^(codim JG))
)

-- Experiments
n = 8;
R = QQ[x_0..x_(n-1)];
elapsedTime ListOfGraphs = generateGraphs(R,MinDegree =>1);
       -- We exclude graphs with isolated vertices.
elapsedTime P = partition(G -> (reg edgeIdeal G == 3), ListOfGraphs);
       -- We restrict graphs whose edge ideal has regularity 3.
length(P#true), length(P#false)
       -- P#true is the list of graphs having regularity 3.

AlphaMin = min \\ alphaValue \ (P#true)
ConjecturedAlphaMinVal = if n%2 == 0 then (n^2-2*n)/(4*(n-2)^2) else (n//2)^2/(n-2)^2
AlphaMin == ConjecturedAlphaMinVal

ConjecturedAlphaMinGraph = alphaValue graph(edges completeGraph((gens R)_{0..(n+1)//2-1})| edges completeGraph((gens R)_{-n//2..-1}))
ConjecturedAlphaMinGraph == ConjecturedAlphaMinVal -- true means it is same!

GraphAlphaMin = select(P#true, G -> (alphaValue G == AlphaMin))

printWidth = 1000
netList for i from 4 to 7 list(
       R := QQ[x_0..x_(i-1)];
       ListOfGraphs := generateGraphs(R,MinDegree =>1);
       P := partition(G -> (reg edgeIdeal G == 3), ListOfGraphs);
       AlphaMin := min \\ alphaValue \ (P#true);
       GraphAlphaMin := select(P#true, G -> (alphaValue G == AlphaMin));
       (AlphaMin, GraphAlphaMin, length(P#true))
)


-- One may be interested in maximum of alpha value.
AlphaMax = max \\ alphaValue \ (P#true)
graphAlpha2 = select(P#true, G -> (alphaValue G == AlphaMax))

-- Experiment for higher dimension
n = 10;
R = QQ[x_0..x_(n-1)];
elapsedTime ListOfGraphs = generateRandomGraphs(R, 1000);
       -- We exclude graphs with isolated vertices.
FilteredListOfGraphs = removeIsomorphs(filterGraphs(ListOfGraphs,{"MinDegree"=>1}));
elapsedTime P = partition(G -> (reg edgeIdeal G == 3), FilteredListOfGraphs);
       -- We restrict graphs whose edge ideal has regularity 3.
length(P#true), length(P#false)
       -- P#true is the list of graphs having regularity 3.

AlphaMin = min \\ alphaValue \ (P#true)
ConjecturedAlphaMin = alphaValue graph(edges completeGraph((gens R)_{0..(n+1)//2-1})| edges completeGraph((gens R)_{-n//2..-1}))
-- ConjecturedAlphaMinVal = if n%2 == 0 then (n^2-2*n)/(4*(n-2)^2) else (n//2)^2/(n-2)^2  
ConjecturedAlphaMin < AlphaMin -- "true" if the conjecture holds

for i from 0 to 100 do (
       ListOfGraphs := generateRandomGraphs(R, 1000);
       FilteredListOfGraphs := removeIsomorphs(filterGraphs(ListOfGraphs,{"MinDegree"=>1}));
       P := partition(G -> (reg edgeIdeal G == 3), FilteredListOfGraphs);
       AlphaMin := min \\ alphaValue \ (P#true);
       print (length(P#true), ConjecturedAlphaMin < AlphaMin)
)


-- (Extra) What happen if we add some conditions on graphs?
-- If we add "Biconnected" condition on graphs, then the followings are graphs having minimum alpha value
-- cycles when |V(G)| is odd.
d = 5;
R = QQ[x_0..x_(d-1)];
G = graph apply(numgens R, i-> {x_i,x_((i+1)%d)})
J = dual \\ monomialIdeal \\ product \ edges G
iniDegJ = initialDegree J
betti res J

-- two simplices connected by two edges when |V(G)| is even.
m = 5; -- size of each component, |V(G)| = 2m
R = QQ[x_0..x_(m-1),y_0..y_(m-1)];
G = graph (subsets(toList(x_0..x_(m-1)),2)|subsets(toList(y_0..y_(m-1)),2)|apply(2,i->{x_i,y_i}))
J = dual \\ monomialIdeal \\ product \ edges G
betti res J
codim J +1 == pdim ((ring J)^1/J) -- it is almost Cohen-Macaulay.

-* 
Experiments
6 vertices, biconnected, regularity = 3: o129 = 1/2 = 7/14
7 vertices, biconnected, regularity = 3: o122 = 7/16
8 vertices, biconnected ,regularity = 3: o107 = 7/18
*-


-- InitialDegree vs degree for rational curves in PP^3
restart
R = ZZ/101[s, t];
S = ZZ/101[x_0..x_3];
netList for a from 3 to 15 list(
f = s^a*t^a*(s+t)^a*(s-t)^a;
F = map(R, S, {s^(4*a+1), t^(4*a+1), s*f, t*f});
I = kernel F;
m = min \\ first \ degree \ (trim I)_*;
(degree I, regularity I, m, sub((degree I)/m^2, RR))
)

-*
--------------------+
o3 = |(13, 8, 6, .361111)  |
     +---------------------+
     |(17, 10, 7, .346939) |
     +---------------------+
     |(21, 12, 8, .328125) |
     +---------------------+
     |(25, 16, 8, .390625) |
     +---------------------+
     |(29, 18, 9, .358025) |
     +---------------------+
     |(33, 20, 10, .33)    |
     +---------------------+
     |(37, 22, 11, .305785)|
     +---------------------+
     |(41, 24, 11, .338843)|
     +---------------------+
     |(45, 26, 12, .3125)  |
     +---------------------+
     |(49, 28, 13, .289941)|
     +---------------------+
     |(53, 30, 13, .313609)|
     +---------------------+
     |(57, 32, 14, .290816)|
     +---------------------+
     |(61, 36, 14, .311224)|
     +---------------------+
*-

sub(1/6, RR) -- Expected value for general curves from theory

---------------------------------------------------------
a=15

loadPackage "MultigradedImplicitization"
componentsOfKernel(3, F)
describe oo

I = kernel(F, SubringLimit => );
codim ideal leadTerm gens I
decompose I
betti I

----------------------------------------------------------
restart
R = ZZ/101[s, t];
S = ZZ/101[x_0..x_3];
K = ideal vars R
netList for d from 10 to 40 list(
I = ker map (R, S, random(toList(4:d),K));
m = min \\ first \ degree \ (trim I)_*;
(degree I, regularity I, m, sub((degree I)/m^2, RR))
)

d=10

-*
 +---------------------+
o4 = |(10, 6, 5, .4)       |
     +---------------------+
     |(11, 6, 6, .305556)  |
     +---------------------+
     |(12, 7, 6, .333333)  |
     +---------------------+
     |(13, 7, 6, .361111)  |
     +---------------------+
     |(14, 8, 7, .285714)  |
     +---------------------+
     |(15, 8, 7, .306122)  |
     +---------------------+
     |(16, 8, 7, .326531)  |
     +---------------------+
     |(17, 8, 8, .265625)  |
     +---------------------+
     |(18, 9, 8, .28125)   |
     +---------------------+
     |(19, 9, 8, .296875)  |
     +---------------------+
     |(20, 9, 8, .3125)    |
     +---------------------+
     |(21, 10, 9, .259259) |
     +---------------------+
     |(22, 10, 9, .271605) |
     +---------------------+
     |(23, 10, 9, .283951) |
     +---------------------+
     |(24, 10, 9, .296296) |
     +---------------------+
     |(25, 11, 10, .25)    |
     +---------------------+
     |(26, 11, 10, .26)    |
     +---------------------+
     |(27, 11, 10, .27)    |
     +---------------------+
     |(28, 11, 10, .28)    |
     +---------------------+
     |(29, 12, 11, .239669)|
     +---------------------+
     |(30, 12, 11, .247934)|
     +---------------------+
     |(31, 12, 11, .256198)|
     +---------------------+
     |(32, 12, 11, .264463)|
     +---------------------+
     |(33, 12, 12, .229167)|
     +---------------------+
     |(34, 13, 12, .236111)|
     +---------------------+
     |(35, 13, 12, .243056)|
     +---------------------+
     |(36, 13, 12, .25)    |
     +---------------------+
     |(37, 13, 12, .256944)|
     +---------------------+
     |(38, 14, 13, .224852)|
     +---------------------+
     |(39, 14, 13, .230769)|
     +---------------------+
     |(40, 14, 13, .236686)|
     +---------------------+
*-

