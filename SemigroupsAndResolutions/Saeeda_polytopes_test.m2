restart
--needsPackage "NumericalSemigroups"
needsPackage "AIWeierstrass"
needsPackage "FourierMotzkin"
needsPackage "Polyhedra"

coneEquations = method(Options => {"Inhomogeneous" => false})
coneEquations ZZ := Matrix => o -> m -> (
        cols :=  flatten for i from 1 to m-1 list
            for j from i to m-1 list {i,j};
        cols = select(cols, p -> sum p != m);
        n := #cols;
        eqns := map(ZZ^(m-1), ZZ^n, (i,j) -> (
            if (sum cols_j -(i+1)) % m == 0 then -1 else if
                cols_j == {i+1,i+1} then 2  else if
                   isMember(i+1, cols_j) and
                   cols_j !={i+1,i+1} then 1 else 0));
        if o#"Inhomogeneous" then
          eqns || matrix{apply(n, j->
                   if sum cols_j < m then 0 else -1)} else
           eqns
      )

  
semigroupFromMu =  mm -> (
    m = #mm+1;
    {m}|apply(#mm, i -> m*mm_i+i+1)
    )

semigroupFromAperySet=method()
semigroupFromAperySet(List) := List => As -> (
   -- As := aperySet L;
   m:=#As+1;
    L:=prepend(m,As);       
    semigroup L)

findSemigroupsAttempt = method()
findSemigroupsAttempt = (m,g) -> (
    G = m*g+(m-1)*m/2;
    
    coneEq = coneEquations m;
    M = (fourierMotzkin coneEq)_0;
    lambdas = apply(flatten entries(matrix{toList(m-1:1)}*M), i -> G/i);

    intPoints :=  latticePoints convexHull(M*diagonalMatrix(lambdas));
    intPoints = select(intPoints, x -> gcd flatten entries x ==1);

    L  :=  for apSet in intPoints list minimalSemigroupGens semigroupFromAperySet flatten entries apSet;
    L=unique L;
    
    SG = select(for elt in L list elt,  x -> #gaps x==g and x#0==m)
)

--comparison

SG1 = findSemigroupsAttempt(4,7);
netList SG1
#SG1
SG1 = findSemigroupsAttempt(4,8);
netList SG1
#SG1
SG1 = findSemigroupsAttempt(4,9);
netList SG1
#SG1
SG1 = findSemigroupsAttempt(4,10);
netList SG1
#SG1
SG1 = findSemigroupsAttempt(5,7);
netList SG1
#SG1
SG = findSemigroupsAttempt(5,8);--discrepancy  here, missing {5,8,12,14} with apSet {16,12,8,14}--multiple of last coneEq, not rel prime
netList SG1
#SG1
SG1 = findSemigroupsAttempt(5,9);
netList SG1
#SG1
SG1 = findSemigroupsAttempt(5,10);--missing {5,9,13,17,21} and {5,6} with apSet {21,17,13,9} (idk issue here) and {6,12,18,24} (not rel prime) resp
netList SG1
#SG1
SG1 = findSemigroupsAttempt(6,7);
SG1 = findSemigroupsAttempt(6,8);
SG1 = findSemigroupsAttempt(6,9);
SG1 = findSemigroupsAttempt(6,10);

netList SG1
#SG1

SG1 = findSemigroupsAttempt(6,13);
netList SG1
#SG1

select(SG1, x -> testNWfWithAllDegreeConditions x)

--meh, findSemigroupsAttempt is subpar not only because of missing semigroups but also because of speed
--vs

restart
needsPackage "NumericalSemigroups"


SG2 = findSemigroups(4,7);
netList SG2
#SG2
SG2 = findSemigroups(4,8);
netList SG2
#SG2
SG2 = findSemigroups(4,9);
netList SG2
#SG2
SG2 = findSemigroups(4,10);
netList SG2
#SG
SG2 = findSemigroups(5,7);
netList SG2
#SG2
SG2 = findSemigroups(5,8);
netList SG2
#SG2
SG2 = findSemigroups(5,9);
netList SG2
#SG2
SG2 = findSemigroups(5,10);
netList SG2
#SG2
SG2 = findSemigroups(6,7);
netList SG2
#SG2
SG2 = findSemigroups(6,8);
netList SG
#SG2
SG2 = findSemigroups(6,9);
netList SG2
#SG2
SG2 = findSemigroups(6,10);
netList SG2
#SG2

SG2 = findSemigroups(6,13);
netList SG2
#SG2

select(SG2, x -> testNWfWithAllDegreeConditions x)



--checking

aperySet {5,9,13,17,21} 
aperySet {5,6}
SG = {5,8,12,14}
AS = aperySet SG
cE = coneEquations SG#0

(matrix  {AS})*cE

SG = {5,9,13,17,21}
AS = aperySet SG
cE = coneEquations SG#0



----scratch

-*
for apSet in LL do (
    as := flatten entries vector {16,16,12,6} 
    as = as/gcd as
    )


    L  :=  for apSet in intPoints list minimalSemigroupGens semigroupFromAperySet flatten entries apSet;
    L=unique L;

*-

m = 5
gen = 9
g = m*gen+(m-1)*m/2

coneEq = coneEquations m
M = (fourierMotzkin coneEq)_0
lambdas = apply(flatten entries(matrix{toList(m-1:1)}*M), i -> g/i)

LL :=  latticePoints convexHull(M*diagonalMatrix(lambdas))
LL = select(LL, x -> gcd flatten entries x ==1)

L  :=  for muSet in LL  list minimalSemigroupGens semigroupFromAperySet flatten entries muSet
L=unique L

--SG :=  select(for elt in L list (elt, #gaps elt), x -> x_1==gen and (x_0)#0==m)
SG = select(for elt in L list elt,  x -> #gaps x==gen and x#0==m)
netList SG
