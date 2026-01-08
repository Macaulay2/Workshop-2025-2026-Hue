restart
needsPackage "Visualize"
viewHelp Visualize
G = graph({{0,1},{0,3},{0,4},{1,3},{2,3}},Singletons => {5})
openPort "8888"
visualize G
-- goal: get this working with Nauty

