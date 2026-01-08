-- using Nauty package
restart
-- load Package "Visualize" BEFORE Nauty
needsPackage "Visualize"
needsPackage "Nauty"
R = QQ[a..f];
E = {{a,b},{b,c},{c,f},{d,a},{e,c},{b,d}}
G = graph(R, E)
copyG = Graphs$graph edges G
openPort "8888"
visualize copyG

-- using GraphRegularity package
restart
path = append(path, "../GraphRegularity/")
-- load Package "Visualize" BEFORE GraphRegularity
needsPackage "Visualize"
needsPackage "GraphRegularity"
R = QQ[a..f];
E = {{a,b},{b,c},{c,f},{d,a},{e,c},{b,d}}
G = graph(R, E)
copyG = Graphs$graph edges G
openPort "8888"
visualize copyG


