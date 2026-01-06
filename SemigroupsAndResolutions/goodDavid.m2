good = value get "good0";
elapsedTime goodTable =  hashTable apply(good,
    L->(semigroupGenus L, L))
gt = new MutableHashTable from goodTable;
for g from 13 to 700 do (
    if g%3==0 then continue else
    gt#g = {6,9,g,g+3})
goodTable = hashTable pairs gt
gene0 = sort keys goodTable;
--missing under 400:
missing = {18,336,351,384, 387, 393}
g = 394; while member(g, gene0) do g = g+1; g
{}==select (for g in missing list (g, member(g, gen)),last)

---
needsPackage "AIWeierstrass"
elapsedTime LL = flatten for g from 13 to 30 list(
L = {6,9,g,g+3};
for r from 0 to 20 list(
    L' = {L_0+2*r, L_1+3*r, L_2+4*r, L_3+5*r};
    if gcd L' !=1 then continue else
    { testNWfWithAllDegreeConditions L',semigroupGenus L'}
    ));
#LL
LLgood = select(LL, L-> L_0_1)
#LLgood
LLnot3 = select(LL, L -> last L %3 == 0)
gen = sort(LLnot3/last)
gen



needsPackage"AIWeierstrass"
L = {11,14,18,21}
elapsedTime LL = for r from 0 to 30 list(
    L' = {L_0+3*r, L_1+4*r, L_2+5*r, L_3+6*r};
    if gcd L' !=1 then continue else
    { testNWfWithAllDegreeConditions L',semigroupGenus L'}
    );
#LL
LLgood = select(LL, L-> L_0_1);
#LLgood
LLnot3 = select(LL, L -> last L %3 == 0)
gen = sort gen|(LLnot3/last)
gen = unique gen
#gen

--the next group seems to have no genera
--that are multiples of 3
L = {14,17,21,24}
elapsedTime LL = for r from 21 to 30 list(
    L' = {L_0+4*r, L_1+5*r, L_2+6*r, L_3+7*r};
    if gcd L' !=1 then continue else
    { testNWfWithAllDegreeConditions L',semigroupGenus L'}
    );
#LL
LLgood = select(LL, L-> L_0_1);
#LLgood
LLnot3 = select(LL, L -> last L %3 == 0)
gen = unique(sort (gen|(LLnot3/last)))
#gen
