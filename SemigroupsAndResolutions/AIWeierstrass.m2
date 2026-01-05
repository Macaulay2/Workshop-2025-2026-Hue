--uninstallPackage "RandomPoints"
--installPackage "RandomPoints"

///
restart
needsPackage "AIWeierstrass"

elapsedTime installPackage "AIWeierstrass"

viewHelp "AIWeierstrass"
viewHelp "FastMinors"
   
check "AIWeierstrass"

restart
uninstallPackage "AIWeierstrass"
restart
installPackage "AIWeierstrass"
check "AIWeierstrass"

viewHelp "AIWeierstrass"

loadPackage ("AIWeierstrass",Reload=>true)
///

newPackage(
         "AIWeierstrass",
         Version => "0.1",
         Date => "August 30, 2025",
         Headline => "Harnessing ML to find Weierstrass semigroups",
         Authors => {{ Name => "David Eisenbud", Email => "de@berkeley.edu", HomePage => "http://eisenbud.github.io"},
	             { Name => "Frank-Olaf Schreyer", Email => "schreyer@math.uni-sb.de", HomePage => "https://www.math.uni-sb.de/ag/schreyer"}},
         Keywords => {"machine learning, Weierstrass points"},
	 PackageExports => {"FastMinors",HomologicalAlgebraPackage,"Permutations","PrimaryDecomposition"},--"NumericalSemigroups"
	 AuxiliaryFiles => false,
         DebuggingMode => true,
         )

     export {
	 "verifyOneParameterFamilies",
	 "WithFastMinors",
	 "UseMaxMinors",
	 "AllDegreeConditions",
	 "Bound",
	 "Factor",
	 "ProbTest",
	 "Bisection",
         "verifyNotWeierstrass",
         "familyWithSection",
	 "BaseField",
	 "numericalProofOfNonWeierstrass",
	 "degreeMatrices",
	 "WithSectionOnly",
	 "subFamilyWithSection",
	 "addData",
	 "addDataToListOfLnW",
	 "testNWfWithAllDegreeConditions",
	 "degreeMatricesOld",
	 "liftToCharacteristicZero",
	 "testSubcomplex",
	 "pseudoFrobenius",
	 
	 
"getFlatFamily", -- partially done, should be revised to cover more cases
"pruneFamily", -- done
"randomFiber", -- need to add documentation mentioning that this
--is only called when the base is affine space.
"testWeierstrass",
"testWeierstrassRange",
"getFiber",
"syzFormat", -- done
"withRandomPoint", -- done
"withComponents", -- done
"withAffineBase", -- done
"restrictedUnfolding", --done should be extended
"def1", --done
"sums",
"isGapSequence",
"gaps",
"findSemigroups",
"isARandomFiberSmooth", -- done, perhaps remove
"ewt", -- done
--"isWeierstrassSemigroup",
"knownExample", -- done
"buchweitzSemigroups", --done
--"buchweitzCriterion", -- add code
--"nonWeierstrassSemigroups",
"heuristicSmoothness", --done, could be removed
"findPoint", -- done
"flatteningRelations", -- done
"makeUnfolding", -- done
"isSmoothableSemigroup", -- should be revised or deleted?

"checkFlatness",-- done
"optimalBound",  -- done, revise for the case L is presumably not a Weierstrass semigroup,
                 -- both code and documantation
"optimalRange",
"prepareInitialPositionList", 
"showRestrictedFamily", --(List,List) := o -> (L,leftPositions) -> (
"systematicShrinking",--(List,List) := o -> (L,initialList) -> (
"reverseSorting",
"reverseSortingB",
"shrinkRange",
"positionListToArray",
"positionArrayToList",
"degreeArray",
"dimSingularLocusOfFiber",
"Probably",-- option for dimSingularLocisOfFiber to use fastMinors
"semigroupRing",
"semigroupIdeal",
"socle",
"type",
"apery",
"aperySet",
--"conductor",
"weight",
"semigroup",
"buchweitz",
"buchweitzCriterion",
"mu",
"semigroupGenus",
"minimalSemigroupGens",
"positiveResidue",
"displayMinimalFamilies",
"dataForML",
"enrichMinListData",
"tagZeroes",
"produceData",
"produceBounds",
"produceRangesFromBounds",
"produceShrinkedRangesFromRanges",
"produceMinListsFromRanges",
"produceMinimalFamiliesFromMinLists",
"produceEasyBounds",
"testEasyBound",
"continueComputation",
"commutativeAlgebra",
"combinatorialFunctions",
"dataFunctions",
"getOptimalBounds",
"getOptimalRanges",
"getMinimalFamilies",
--"trainingData",
"LabBookProtocol",
--"verifyTrainingData",
"minimalPositionLists",
"testNW",
--"testNWf",
--"testNWk",
"getFromDisk",
"ls",
"computeLL4wS",
"forSergeiAndGiorgi",
"makeArithmeticProgression",
"testNWListOfLists",
"kunzIdeal",
"kunzWaldi",
}

     -* Code section *-
-* data functions *-


///
restart
needsPackage "AIWeierstrass"
(L, posList) = ({6, 8, 10, 11, 13}, {10, 32, 55, 74, 85, 102})
tD={({4, 7, 9, 10}, {22, 23, 35, 36, 64, 65}), ({4, 7, 9, 10}, {1, 23, 36, 49, 64, 65})}
displayMinimalFamilies tD
dL =  dataForML (L,posList);
dL_1
apply (3, i -> (<<netList dL_i<<endl));
dL_3
dL_4
g=semigroupGenus L
guess=g+2
elapsedTime b=optimalBound (L,guess,Verbose => true, Probably => true)
elapsedTime range=optimalRange(L,b,Verbose => true, Probably => true)
elapsedTime fLs=minimalPositionLists(L,range,2,Verbose=>true,Probably=>true)
displayMinimalFamilies(apply(fLs,fL->(L,fL)))
///

verifyOneParameterFamilies=method(Options=>{Verbose=>true,WithFastMinors=>false,UseMaxMinors=>1000})
verifyOneParameterFamilies(List) := o -> LLI -> (
    I:= null; L:= null; S:= null; flat:=null; S10007:=null;
    I1:=null;smooth:=null;R:=null;
    apply(LLI, IL -> (
	I=ideal IL_0;
	L=flatten drop(IL_1,-1);
	S=QQ[support I,Degrees=>IL_1];
	flat = betti res sub(I,S) == betti res semigroupIdeal L;
	I1=sub(I,last gens S=>1);
	S10007=ZZ/10007[support I1];
	R=S10007/sub(I1,S10007);
	if o.Verbose then (
	    <<" semigroup = "<<L<<flush<<endl;
	    if not o.WithFastMinors then (
	    elapsedTime smooth = dim singularLocus R==-1) else (
	    elapsedTime smooth = regularInCodimension(1,R,MaxMinors=>o.UseMaxMinors));
	    <<"flat = "<<flat<<", smooth = " << smooth <<flush<<endl;) else (
	    if not o.WithFastMinors then (
	         smooth = dim singularLocus R==-1) else (
	         smooth = regularInCodimension(1,R,MaxMinors=>o.UseMaxMinors));
	    );
	(L,flat and smooth)))
    )


	    
	    
	
    
    



/// -* test verify
OneParameterFamily *-
LL10I=value get "LL10as";
first LL10I
LLI=LL10I_{0..9};
verifyOneParameterFamilies LLI

///

dataForML = method()
dataForML(List, List) := List => (L,posList) -> (
    I := semigroupIdeal L;
    (A,unfolding) := makeUnfolding I;
    posAll := positionListToArray(L,toList(0 ..  numgens A -1));
    degAll := degreeArray(L, posAll);
    degMinList :=degreeArray(L, positionListToArray(L, posList));
    range:=toList(min flatten degMinList..max flatten degMinList);
    posInitial:=prepareInitialPositionList(L,range);
    posRange := positionListToArray(L,posInitial);
    degRange := degreeArray(L, posRange);
    sF := syzFormat L;
    B := betti res I;
     {degAll, degRange, degMinList, sF,B}
    )

tagZeroes=method()
-- Input: degArray, List, "double nested" lists of lists
-- Output: M,Matrix of degrees, 0 means "no entry"
tagZeroes(List) := degArray -> (
    m:=max apply(degArray ,row -> #row);
    matrix apply(degArray,row -> row|{m-#row:0})
    )
///
tagZeroes({{2,1},{3,2,1}})==matrix{{2,1,0},{3,2,1}}

///

enrichMinListData = method()
enrichMinListData(List, List) := List => (L,posList) -> (
    I := semigroupIdeal L;
    (A,unfolding) := makeUnfolding I;
    posAll := positionListToArray(L,toList(0 ..  numgens A -1));
    degAll := degreeArray(L, posAll);
    degMinList :=degreeArray(L, positionListToArray(L, posList));
    range:=toList(min flatten degMinList..max flatten degMinList);
    posInitial:=prepareInitialPositionList(L,range);
    posRange := positionListToArray(L,posInitial);
    degRange := degreeArray(L, posRange);
    sF := syzFormat L;
    B := betti res I;
    bettiKeys:=sort apply(keys B,k->(k_0,k_2));
    {(gaps L, semigroupGenus L, ewt L),
	(#flatten degAll,#flatten degRange, #flatten  degMinList),
	(tagZeroes degAll, tagZeroes degRange, tagZeroes degMinList),
	(L,sF,bettiKeys)}    
    )
enrichMinListData(List) :=List => LLMinLists -> apply(LLMinLists,D->enrichMinListData(D_0,D_1))

///
LLMinLists=flatten getFromDisk("tD6new");
LLMinLists=reverse sort(LLMinLists,D->ewt D_0);
netList enrichMinListData(LLMinLists)
///

produceData=method(Options=>{Verbose=>false, "KillFile" =>false})
-- Input: List of semigroups
-- Output: List of training data (L,minList)

produceData(List,String) := List => o-> (LL,name)->(
minLists:=null;D:=null;g:=null;L:=null;
if member(name, openFiles()) then
    (name << close;
    if o#"KillFile" then removeFile name);
if o.Verbose then (elapsedTime dL:=flatten apply(#LL,i->(
    L=LL_i;
    g=semigroupGenus L;
    <<flush<<endl;
    <<"case = " << i <<", semigroup = " <<L <<flush<<endl;
    (elapsedTime minLists=minimalPositionLists(
	 L,g+2,3,Verbose=>o.Verbose,Probably=>true));
    if class minLists === Nothing then(
	<<"example #"<<i<< "with semigroup "<<L<<" could not find
	a point; we skipped it"<<flush<<endl;
    D = {L," is an example where findPoint failed"}) else(
    openOutAppend name;
    D=apply(minLists,mL->(L,mL));
    name<<D;
    name << ", ";    name<<close);
    D))) else (
    dL=flatten apply(#LL,i->(    
    L=LL_i;
    g=semigroupGenus L;
    <<flush<<endl;
    <<"case = " << i <<", semigroup = " <<L <<flush<<endl;
    minLists=minimalPositionLists(
	 L,g+2,3,Verbose=>o.Verbose,Probably=>true);
    if class minLists === Nothing then(
	<<"example #"<<i<< "with semigroup "<<L<<" could not find
	a point; we skipped it"<<flush<<endl;
    D = {L," is an example where findPoint failed"}) else(
    openOutAppend name;
    D=apply(minLists,mL->(L,mL));
    name<<D;
    name << ", ";    name<<close);
    D)));
dL)

produceData(List,ZZ,String) := List => o-> (LL,n,name)->(
minLists:=null;D:=null;g:=null;L:=null;
if member(name, openFiles()) then
    (name << close;
    if o#"KillFile" then removeFile name);
if o.Verbose then (elapsedTime dL:=flatten apply(#LL,i->(
    L=LL_i;
    g=semigroupGenus L;
    <<flush<<endl;
    <<"case = " << i <<", semigroup = " <<L <<flush<<endl;
    (elapsedTime minLists=minimalPositionLists(
	 L,g+2,n,Verbose=>o.Verbose,Probably=>true));
    if class minLists === Nothing then(
	<<"example #"<<i<< "with semigroup "<<L<<" could not find
	a point; we skipped it"<<flush<<endl;
    D = {L," is an example where findPoint failed"}) else(
    openOutAppend name;
    D=apply(minLists,mL->(L,mL));
    name<<D;
    name << ", ";    name<<close);
    D))) else (
    dL=flatten apply(#LL,i->(    
    L=LL_i;
    g=semigroupGenus L;
    <<flush<<endl;
    <<"case = " << i <<", semigroup = " <<L <<flush<<endl;
    minLists=minimalPositionLists(
	 L,g+2,3,Verbose=>o.Verbose,Probably=>true);
    if class minLists === Nothing then(
	<<"example #"<<i<< "with semigroup "<<L<<" could not find
	a point; we skipped it"<<flush<<endl;
    D = {L," is an example where findPoint failed"}) else(
    openOutAppend name;
    D=apply(minLists,mL->(L,mL));
    name<<D;
    name << ", ";    name<<close);
    D)));
dL)



produceBounds=method(Options=>{Verbose=>false, "KillFile" =>false})
-- Input: List of semigroups
-- Output: List of training data (L,bound)

produceBounds(List,String) := o -> (LL,name)->(
D:=null;g:=null;L:=null;bound:=null;
if member(name, openFiles()) then
    (name << close;
    if o#"KillFile" then removeFile name);
    nameF:=name|"Failure";
    dLbounds:=apply(#LL,i->(
    L=LL_i;
    g=semigroupGenus L;
    <<flush<<endl;
    <<"case = " << i <<", semigroup = " <<L <<flush<<endl;
    elapsedTime bound=optimalBound(L,g+2,Verbose=>o.Verbose,Probably=>true);
    if class bound === Nothing then (
	<<"example #"<<i<< "with semigroup "<<L<<" could not find
	a point; we write it to a seperate file"<<flush<<endl;
    D = {L," is an example where findPoint failed"};
    openOutAppend nameF;
    nameF<<LL_i;
    nameF << ", ";    nameF<<close;
    ) else (
    D=(L,bound));
    openOutAppend name;
    name<<D;
    name << ", ";    name<<close;
    D));
dLbounds)

produceRangesFromBounds = method(Options =>{Verbose =>false,"KillFile" =>false})

produceRangesFromBounds(List,String) :=  o-> (LL,name)->(
D:=null;g:=null;L:=null;range:=null;optB:=null;
if member(name, openFiles()) then
    (name << close;
    if o#"KillFile" then removeFile name);
    nameF:=name|"Failure";
    dLranges:=apply(#LL,i->(
    L=LL_i_0; optb:=LL_i_1;
    g=semigroupGenus L;
    <<flush<<endl;
    <<"case = " << i <<", semigroup = " <<L <<flush<<endl;
    elapsedTime range = optimalRange(L,optb,Probably=>true);
    if class range === Nothing then (
	<<"example #"<<i<< "with semigroup "<<L<<" could not find
	a point; we write it to a seperate file"<<flush<<endl;
    D = {L," is an example where findPoint failed"};
    openOutAppend nameF;
    nameF<<LL_i;
    nameF << ", ";    nameF<<close;
    ) else (
    D=(L,range));
    openOutAppend name;
    name<<D;
    name << ", ";    name<<close;
    D));
dLranges)

produceShrinkedRangesFromRanges = method(Options =>{Verbose =>false,"KillFile" =>false})

produceShrinkedRangesFromRanges(List,String) := o -> (LLR,name)->(
D:=null;g:=null;L:=null;range:=null;optB:=null;sRange:=null;
if member(name, openFiles()) then
    (name << close;
    if o#"KillFile" then removeFile name);
    dLranges:=apply(#LLR,i->(
	    L=LLR_i_0; range=LLR_i_1;
	    <<flush<<endl;
	    <<"case = " << i <<", semigroup = " <<L <<flush<<endl;
	    elapsedTime sRange = shrinkRange(L,range);
	    D=(L,sRange);
    openOutAppend name;
    name<<D;
    name << ", ";    name<<close;
    D));
dLranges)


produceMinListsFromRanges=method(Options=>{Verbose=>false, "KillFile" =>false})
-- Input: List of pairs (L,range) semigroups and a optimal range
--       n integer, how many atemps to find different min lists
-- Output: List of training data (L,minList)

produceMinListsFromRanges(List,ZZ,String) :=  o-> (LL,n,name)->(
D:=null;g:=null;L:=null;range:=null;minList:=null;fL:=null;minLists:=null;
if member(name, openFiles()) then
    (name << close;
    if o#"KillFile" then removeFile name);
    nameF:=name|"Failure";
    elapsedTime dLMinLists:=apply(#LL,i->(
    L=LL_i_0; range=LL_i_1;
    g=semigroupGenus L;
    <<flush<<endl;
    <<"case = " << i <<", semigroup = " <<L <<flush<<endl;
    elapsedTime minLists = minimalPositionLists(L,range,n);
    --<<minLists<<endl;
    if class minLists === Nothing then (
	<<"example #"<<i<< " with semigroup "<<L<<" could not find
	a point; we skipped it"<<flush<<endl;
    openOutAppend nameF;
    nameF<<LL_i;
    nameF << ", ";    nameF<<close;
    ) else (
    D=apply(minLists,fL->(L,fL));
    openOutAppend name;
    name<<D;
    name << ", ";    name<<close;
    D)));
dLMinLists)

produceMinimalFamiliesFromMinLists = method(Options=>{Verbose=>true})
produceMinimalFamiliesFromMinLists(List,String):=  o -> (LL,name) -> (
D:=null;g:=null;L:=null;pos:=null;fL:=null;family:=null;J:=null;
if member(name, openFiles()) then
    name << close;
    elapsedTime dLMinFams:=apply(#LL,i->(
    L=LL_i_0; pos=LL_i_1;
    <<flush<<endl;
    <<"case = " << i <<", semigroup = " <<L <<flush<<endl;
    elapsedTime (J,family)=toSequence (showRestrictedFamily(L,pos))_{0,1};
    --<<minLists<<endl;
    D:=(L,family,J);
    openOutAppend name;
    name<<D;
    name << ", ";    name<<close;
    D));
dLMinFams)

liftToCharacteristicZero = method(Options=>{Verbose=>true})

liftToCharacteristicZero(List,Matrix,Ideal) := o -> (L,fam,J) -> (
    if not J==0 and o.Verbose then (<<"number of flattening relations = " << numgens J<<", first Equation = "<<J_0
	<<flush<<endl;);
    kk:= coefficientRing ring fam;
    SAQQ:=QQ[support fam,Degrees=>support fam/degree];
    (MJ,CJ) := coefficients gens J;
    TC:=tally flatten entries CJ;
    if max apply(flatten entries CJ,c->abs sub(c,ZZ)) >100 then (
	<<"large coefficients of J = " <<TC<<flush<<endl;return null); 
    (M,C):=coefficients fam;
    T:=tally flatten entries C;
    if max apply(flatten entries C,c->abs sub(c,ZZ)) >100 then (
	<<"large coefficients = " <<T<<flush<<endl;return null);
    
    IQQ:=ideal sub(fam,SAQQ/sub(J,SAQQ));
    return(
	betti res semigroupIdeal(L,BaseField=>QQ)==betti res(IQQ,LengthLimit => #L)
	)
    )

///
restart
needsPackage "AIWeierstrass"
LL=select(findSemigroups 4,L->#L>2);#LL
LL=reverse sort(LL,L->ewt L);
apply(LL,L->(ewt L,L))
LL=LL_{0,1};#LL;
name="tmp"
elapsedTime tD=produceData(LL,name)
td=flatten drop(toList value get name,-1)
tD==td
run "rm tmp"

name="tempB"
elapsedTime tB=produceBounds(LL_{0},name)
continueComputation(produceBounds,LL,name)
tb=flatten drop(toList value get name,-1)

name="tempR"
elapsedTime tR=produceRangesFromBounds(tb,name)

name="tempL"
elapsedTime tL=produceMinListsFromRanges(tR_{0},3,name)
displayMinimalFamilies flatten tL

F=produceMinListsFromRanges
continueComputation(F,tR,name)
drop(toList value get name,-1)
displayMinimalFamilies flatten tD
run "rm tempB tempR tempL"
///
continueComputation=method(Options=>{Verbose=>false}) 

continueComputation(Function,List,String) := o -> (F,LL,name) -> (
    done:=getFromDisk name;
    if class first done === List then done=flatten done;
    LLdone:=apply(done,D->D_0);
    LLtodo :=if class first LL === Sequence then (
	select(LL,D->not member(D_0,LLdone))) else (
	select(LL,L->not member(L,LLdone)));
    F(LLtodo,name)
    )

continueComputation(Function,List,ZZ,String) := o -> (F,LL,n,name) -> (
    done:=getFromDisk name;
    if class first done === List then done=flatten done;
    LLdone:=apply(done,D->D_0);
    LLtodo :=if class first LL === Sequence then (
	select(LL,D->not member(D_0,LLdone))) else (
	select(LL,L->not member(L,LLdone)));
    if F===produceMinListsFromRanges then return F(LLtodo,n,name);
    F(LLtodo,name)
    )


///
debug needsPackage "AIWeierstrass"
{8, 9, 11, 12, 13, 14, 15}
F = produceBounds
F===produceMinListsFromRanges
name = "bounds8"
n=0
LL =select(reverse sort (findSemigroups 8, weight), L -> #L>2)
position(LL, L -> L == {8, 9, 11, 12, 13, 14, 15})
continueComputation(F, LL, 0, name)


tdb8 = drop (toList value get "bounds8", -1)
tdb8/(L -> semigroupGenus (L_0))
tally oo
LL = (select(findSemigroups 8, L->#L>2));#LL
LL_{62..65}
done = apply(tdb8, L -> L_0)
notDone = select(LL, L-> not member(L, done));#notDone
notDone/ewt
netList notDone

///

testEasyBound=method(Options=>{Verbose=>false})

testEasyBound(List,ZZ) := o -> (L,d) -> (
    g:=semigroupGenus L;
    if o.Verbose then (
	elapsedTime ans:=testWeierstrass(L,g+d,Verbose=>o.Verbose)) else (
	ans=testWeierstrass(L,g+d));
    ans)

produceEasyBounds = method(Options=>{Verbose => false,"KillFile" =>true})
-- Input: a List of semigroups
--        d integer
-- Output a list of pairs (L,b)
--        where b is an optimal bound for L larger then g(L)+d
produceEasyBounds(List,ZZ,String) := o -> (LL,d,name) -> (
    if member(name, openFiles()) then (name << close;
    if o#"KillFile" then removeFile name);
    g:=null;ans:=0;b:=null;L:=null;
    data:=for i from 0 to #LL-1 list (
	L=LL_i;
	<<"case = " <<i<<", semigroup = " <<L <<flush <<endl;
	g=semigroupGenus L;
	ans = testEasyBound(L,g+d);--,Verbose=>o.Verbose);
	<<ans<<endl;
	if class ans === Nothing then continue;
	if ans == 0 then continue;
	b=optimalBound(L,g+d+2,Verbose=>o.Verbose);
	openOutAppend name;
	name<<(L,b);
	name << ", "; name <<close;
	(L,b));
    data)
	

///   
restart
needsPackage "AIWeierstrass"

g=10
LL=select(findSemigroups g, L-> (not knownExample L and min L>5) );
#LL
LL=LL_{8,9}
run "ls -ltr"
--run "rm stepBounds"
name="stepBounds"
name|"Failures"
class o8
elapsedTime dLbounds=produceBounds(LL,name)
dLbounds1=drop(toList value get name,-1)
dLbounds1==
dLbounds

name="stepRanges"
elapsedTime dLRanges=produceRangesFromBounds(dLbounds,name)
dLRanges=drop(toList value get "stepRanges",-1)
name="stepMinLists"
n=3
elapsedTime dLMinLists=produceMinListsFromRanges(dLRanges,n,name)
value get "stepMinLists"
displayMinimalFamilies(flatten dLMinLists)

name="easyBounds10"
openFiles()
run "ls -ltr"
run "rm easyBounds9"
elapsedTime easyB=produceEasyBounds(LL,-4,name,Verbose=>false)
eB=drop(toList value get "easyBounds10",-1)
#eB

g=11
--from 2024 attempt
LLdifficult={{6, 8, 17, 19, 21},
    {6, 8, 10, 19, 21, 23},
    {6, 9, 11, 14},{8, 9, 11, 15, 21}}
L = first LLdifficult
betti res semigroupIdeal L
range=for i from 1 to 13 list i*3 
elapsedTime testWeierstrassRange (L, {3,6,9,39}, Verbose => true, Probably=>true)


g=12
LL=select(findSemigroups g,L->(not knownExample L) and min L>5);#LL
#LL*7.4/60
elapsedTime LLeasy=select(LL,L->(
	elapsedTime ans=testWeierstrass(L,g,Probably=>true);
	<<L<<": dim sing = "<<ans<<flush<<endl;
	if class ans=!=Nothing then ans ==-1 else false));
#LLeasy


LL12easy
LL=findSemigroups g;#LL
LL=select(LL,L->not knownExample L);#LL
LLeasy=select(LL,L->not member(L,LLdifficult));#LLeasy
run "ls -ltr"
bounds11easy=drop(toList value get "bounds11easy",-1)
bounds11done=apply(bounds11easy,LB->LB_0)
LLeasy2=select(LLeasy,L->not member(L,bounds11done))
name="bounds11easy2"
elapsedTime produceBounds(LLeasy,name,Verbose=>true)

elapsedTime apply(LLdifficult,L->elapsedTime testWeierstrass(L,0,Verbose=>true,Probably=>true))


///
///
restart
debug needsPackage "AIWeierstrass"
g=5
LL=findSemigroups(g); #LL
LL = select(LL, L-> #L>2);#LL

LL = select(LL, L-> #L == 4);#LL
LL = select(LL,L-> syzFormat L =={1, 6, 8, 3});#LL
LL_10 ==
L = {4, 14, 17, 23}
--this crashed the version before we fixed the null problem.
netList apply({L}, L-> (
	fL = res semigroupIdeal L;
	(L, fL.dd_3, flatten degrees fL_3)
	))
#LL
LL=select(LL,L->#L>2); #LL
dL = produceData(LL_{1,2},"tmp1", "KillFile" => true)
dL = produceData(LL_{3},"tmp1", "KillFile" => false)
dL = produceData(LL_{11..38},"g12e4From11", "KillFile" => false)

outList = drop (flatten toList value get "tmp1", 1)
displayMinimalFamilies outList

run "ls"
run "rm tmp tmp1"
dataTemp
dL6=flatten dL
-*
run "git commit -am'try'"
run "git status"
run "git push"
*-
viewHelp File
openOutAppend "tmp"
"tmp"<<{}
"tmp"<<{1}
"tmp"<<close
"tmp"<<kill
get "tmp"
    
///
getFile = method()
getFile String := fileName -> get fileName

/// -* [test Data ] *-
needsPackage"AIWeierstrass"
tD = (trainingData("optimalBound" ))_{10..12}
#tD
tally apply(tD, D -> semigroupGenus D_0)
elapsedTime verifyTrainingData("optimalBound", tD, Verbose => true)
elapsedTime verifyTrainingData("optimalBound", 10)

---File creation
restart
needsPackage "AIWeierstrass"

gaps last findSemigroups 10


optimalBoundsData = method(
    Options => {Verbose => true, Probably => true})
optimalBoundsData (ZZ,ZZ, String) := File => o-> (g,guess, fileName)-> (
LL := drop(findSemigroups g, -1);
--LL = select(LL, L -> #L >2);
LL = select(LL, L-> not knownExample L);
if o.Verbose then <<"number of cases = "<<#LL<<flush<<endl;
td := {};
B := null;

tD := apply(#LL, i ->(
    L = LL_i;
    <<endl;
    << "case = "<<i<<", semigroup = "<<L<<flush<<endl;
    if o.Verbose then elapsedTime B = optimalBound(L, guess, o) else
        B = optimalBound(L, guess, o);
    td = append(td,(L,B));
    (L,B)
    ));

if o.Verbose then <<netList tD<<flush <<endl;
f := fileName;
openOut f;
f<<toExternalString tD;
f<<close;
)

elapsedTime optimalBoundsData(9,10,"bounds9") -- 246 sec
apply(B, b-> optimalRange(b_0,b_1, Verbose => true, Probably => true)
)

optimalRangeData = method(
    Options => {Verbose => false, Probably => true})

optimalRangeData(List, String) := File => o-> (LBs, fileName)-> (
if o.Verbose then <<"number of cases = "<<#LBs<<flush<<endl;
td := {}; B := null; L := null;lowerbound := null;I := null;
maxDeg := null;

tD := apply(#LBs, i ->(
    L = LBs_i_0;
    lowerBound = LBs_i_1;
    <<endl;
    I = semigroupIdeal L;
    maxDeg = (max (I_*/degree))_0;
    << "case = "<<i<<",semigroup = "<<L<<
    ", lowerBound = " << lowerBound <<
    ", maxDeg = " <<maxDeg <<flush<<endl;
    if o.Verbose then 
        elapsedTime range = optimalRange(L, lowerBound, o) else
        range = optimalRange(L, lowerBound, o);
    td = append(td,(L,range));
    (L,range)
    ));

if o.Verbose then <<netList tD<<flush <<endl;
f := fileName;
openOut f;
f<<toExternalString tD;
f<<close;
)

optimalRangeData (B,"ranges9")

netList (B= value get "ranges9")

tally apply(B,D->(
--	D=B_0
    L=D_0;
    range= D_1;
    posList=prepareInitialPositionList(L,range);
    posArray=positionListToArray(L,posList);
    degArray=degreeArray(L,posArray);
    <<" semigroup = " <<L<< ", degArray = " << netList degArray <<flush <<endl;
    (#L,#posList))
)

Bsorted=sort(B,D->(
    L=D_0;range= D_1;
    posList=prepareInitialPositionList(L,range);
    #posList))


netList Bsorted
netList  apply(Bsorted,D->(L=D_0;range=D_1;
	posList=prepareInitialPositionList(L,range);
	posArray=positionListToArray(L,posList);
        degAr=degreeArray(L,posArray);
    (#posList,#range,min L,L,netList degAr))
)



--------------------------------------

    netList (B= value get "bounds9")
0.0+sum(apply(B, B -> B_1))/#B

B8/(B -> B_1)

tD = value get f
elapsedTime verifyTrainingData("optimalBound",tD, Verbose =>true)

tD10=trainingData("optimalBound",10)
#tD10
td={}
elapsedTime netList( tD = apply(#tD10, i ->(
    L = tD10_i_0;b=tD10_i_1;
    <<endl;
    << "case = "<<(i,L)<<flush<<endl;
    elapsedTime B = optimalBound(L, b, Verbose => true,Probably=>true);
    td = append(td,(L,B));
    (L,B)
    )))
///

minimalPositionLists=method(Options=>{Verbose=>false,Probably=>true})

minimalPositionLists(List,List,Number) := o -> (L,range,n) -> (
    -- input: L semigroup
    --       range, a degree range
    --       n , number of desired minimal position lists
    -- output: a list of up to n distinct minimal position lists
    posList := prepareInitialPositionList(L,range);
--    assert(testWeierstrass(L,posList,Probably=>true)==-1);
    if o.Verbose then (posArray:=positionListToArray(L,posList);
	<<"degree array = "<<netList (degArray:=degreeArray(L,posArray))<<flush<<endl;);
    I:=semigroupIdeal (L,BaseField=> ZZ/nextPrime 10^4);

    (A,unfolding):=makeUnfolding I;
    assert(#support unfolding-#support I==numgens A);
    xs:=(support unfolding)_{0..#L-1};
    as:=apply(numgens I,i->select(support (unfolding_{i}),m->not member(m,xs)));

    --remove variables which have to be zero
    restrictionList:=(apply(flatten as,m->sub(m,A)))_posList;
    if restrictionList == {} then complist := flatten as else
    compList := select(flatten as,m->not(sub(m,A)%ideal restrictionList==0));
--    <<"complist = "<<compList<<flush<<endl;
    runf:=unfolding%ideal compList;
    assert(#support runf-#L==#posList);
    J:=flatteningRelations(I,A,runf);
    betti(Jt:=trim J);   
    initList:=posList_(positions((flatten as)_posList,m->not sub(m,A)%Jt==0));

--assert(testWeierstrass(L,initList,Probably=>true)==-1);

    -- if o.Verbose then <<netList degreeArray(L,positionListToArray(L,initList))<<flush<<endl;
    -- determine variable (positions) which cannot be deleted
    smallerList:=null;
    keepList:=for i in initList list (
	smallerList=delete(i,initList);
	tW := testWeierstrass(L,smallerList,Verbose=>o.Verbose,Probably=>true);
	if o.Verbose then <<"class of tW =" <<class tW <<flush<<endl;
	if class tW === Nothing then return null;
	if tW ==0 then i else break);
    possibleRemovableList := select(initList,i->not member(i,keepList));
    if o.Verbose then <<"keepList = "<<keepList<<endl<<flush;
    if o.Verbose then <<"possibleRemovableList = "<<possibleRemovableList<<endl<<flush;
    if o.Verbose then (
	elapsedTime finListA := systematicShrinking(L,(reverse possibleRemovableList)|keepList,Verbose=>o.Verbose,Probably=>true);) else (
	finListA = systematicShrinking(L,possibleRemovableList|keepList,Verbose=>false,Probably=>true););
    if o.Verbose then <<"finListA = "<< finListA<<flush<<endl;

    minLists:=if class finListA =!= Nothing then(
              if o.Verbose then <<
              netList degreeArray(L,
		      positionListToArray(L,finListA))
                      <<flush<<endl;
               {finListA}) else {};

    if n>1 then (
	if o.Verbose then (
	elapsedTime finListB := systematicShrinking(L,(reverse possibleRemovableList)|keepList,Verbose=>false,Probably=>true);) else (
	finListB= systematicShrinking(L,reverseSorting(L, possibleRemovableList)|keepList,Verbose=>false,Probably=>true););
        if class finListB =!= Nothing then(
            minLists = append(minLists,finListB));
    m:=n-2;
    finListC:= null;
    while m>0 do (randPerm:=apply(toList randomPermutation(#possibleRemovableList),i->i-1);
	if o.Verbose then (
	elapsedTime finListC=systematicShrinking(L,(possibleRemovableList)_randPerm|keepList,Verbose=>false,Probably=>true);) else (
	finListC= systematicShrinking(L,(possibleRemovableList)_randPerm|keepList,Verbose=>false,Probably=>true););
        if class finListC =!= Nothing then(
            minLists = append(minLists, finListC));
        m=m-1);
    minLists = unique apply(minLists, L-> sort L);
    --if o.Verbose then (
	<<"Length of the minimal lists = "<<
    tally apply(minLists,fL->#fL)
    <<flush<<endl;
    --)
    minLists))

minimalPositionLists(List,ZZ,Number) := o -> (L,guess,n) -> (
    -- input: L semigroup
    --        guess, a guess for the optimalBound(L)
    --       n , number of desired minimal position list
    -- output: a list of upto n distince minimal position lists
    b:=optimalBound(L,guess,o);
    if class b === Nothing then return null;
    range := optimalRange(L,b,o);
    if class range === Nothing then return null;
    minList:=minimalPositionLists(L,range,n,o);
    if o.Verbose and not (class minList === Nothing) then (
    << "Length of the minimal position lists = " << tally apply(minList,fL->#fL)<<flush<<endl;);
    minList)
getFromDisk = method()
getFromDisk String := name -> drop(toList value get name,-1)
///
bounds11m2=drop(toList value get "bounds11easy",-1)
#bounds11m2
last bounds11m2
LL=select(findSemigroups 11,L-> not knownExample L);
#LL
first bounds11m2

tdb = getFromDisk "bounds9"
netList keys tally apply(tdb,LB->( 
	L=LB_0; b=LB_1;--I=semigroupIdeal L;
	(b,#L)))

average=sum(tdb,LB->( 
	L=LB_0; b=LB_1;--I=semigroupIdeal L;
	b))/#tdb+0.0
median=(A=sort apply(tdb,LB->( 
	L=LB_0; b=LB_1;--I=semigroupIdeal L;
	b));(A_(floor(#A/2))+A_(ceiling(#A/2)))/2+0.0)

///


/// -* [checkMinimalPositionsLists] *-
restart
debug needsPackage "AIWeierstrass"
L = {3,10,11}
g = semigroupGenus L

range = {10,11}
setRandomSeed("different")

minimalPositionLists(L, range, 2, Verbose => false)
minimalPositionLists(L, range, 5, Verbose => true)


systematicShrinking(L,{3, 4, 18, 19, 34, 35},
                 Verbose => false, Probably => true)
testWeierstrass(L, {4, 18, 19, 34, 35},Verbose => false, Probably => true)
///
reverseSorting=method()
reverseSorting(List,List) := (L,posList) -> (
     -- Input: L semigroup
     --        posList, positionList
     -- Output: resotredPositionList, List
     --
     flatten reverse positionListToArray(L,posList))

reverseSortingB=method()
reverseSortingB(List,List) := (L,posList) -> (
     -- Input: L semigroup
     --        posList, positionList
     -- Output: resortedPositionList, List
     --
     flatten apply(positionListToArray(L,posList),N->reverse N))
///
restart
needsPackage "AIWeierstrass"
--ls()
netList (tL6=flatten getFromDisk "tD6new");
tL6_0
--displayMinimalFamilies tL6
(L,fL)=(select(tL6,D->D_0=={5, 8, 9, 11, 12}))_0
range=sort unique flatten degreeArray(L,positionListToArray(L,fL))


range = {8,9,10}

initList=sort prepareInitialPositionList(L,range)
netList degreeArray(L,positionListToArray(L,initList))

elapsedTime fLa=sort systematicShrinking(L,initList)--, -- 107.174s elapsed
                 Verbose => true, Probably => true)
netList degreeArray(L,positionListToArray(L,fLa))  -- 112.847s elapsed  -- 145.945s elapsed

	     
elapsedTime fLb=sort systematicShrinking(L,reverseSorting(L,initList))--,   -- 94.56s elapsed
                 Verbose => true, Probably => true)
netList degreeArray(L,positionListToArray(L,fLb))  -- 81.5678s elapsed  -- 91.7346s elapsed

elapsedTime fLc=sort systematicShrinking(L,reverseSortingB(L,initList))--,  -- 92.2749s elapsed
                 Verbose => true, Probably => true)
netList degreeArray(L,positionListToArray(L,fLc))   -- 99.5444s elapsed  -- 101.461s elapsed
	     

elapsedTime fLd=sort systematicShrinking(L,reverse initList)--,  -- 78.0858s elapsed
                 Verbose => true, Probably => true)
netList degreeArray(L,positionListToArray(L,fLd)) -- 74.5133s elapsed -- 76.2852s elapsed

elapsedTime testWeierstrass(L,fLd) -- .89723s elapsed

netList (gensInfo=apply(tL6,D->(
	L=D_0;mL=D_1;I=semigroupIdeal L;
	rangeL=flatten degreeArray(L,positionListToArray(L,mL));
	range=toList(min rangeL.. max rangeL);
	initList=prepareInitialPositionList(L,range);
	(A,unfolding)=makeUnfolding L;
	Ab=select(gens A,m->(degree m)_0 >min rangeL);
	(Ar,runf)=restrictedUnfolding(I,initList);
	(Al,runf)=restrictedUnfolding(I,mL);
        elapsedTime ans=testWeierstrass(D_0,D_1,Probably=>true);
	<<"(L,fL)= " <<D<<flush<<endl;
	<<" (A, Ab,Ar,Al) = "<<(#gens A,#Ab,#gens Ar,#gens Al)
	      << ", dim Sing = " << ans <<flush<<endl;
	(gaps L,(#gens A,#Ab,#gens Ar,#gens Al),ans))))

netList (gensInfo=apply(tL6_{18,19,20,20,20},D->(
	L=D_0;mL=D_1;I=semigroupIdeal L;
	rangeL=flatten degreeArray(L,positionListToArray(L,mL));
	range=toList(min rangeL.. max rangeL);
	initList=prepareInitialPositionList(L,range);
	(A,unfolding)=makeUnfolding L;
	Ab=select(gens A,m->(degree m)_0 >min rangeL);
	(Ar,runf)=restrictedUnfolding(I,initList);
	(Al,runf)=restrictedUnfolding(I,mL);
        elapsedTime ans=testWeierstrass(D_0,D_1,Probably=>true);
	<<"(L,fL)= " <<D<<flush<<endl;
	<<" (A, Ab,Ar,Al) = "<<(#gens A,#Ab,#gens Ar,#gens Al)
	      << ", dim Sing = " << ans <<flush<<endl;
	(gaps L,(#gens A,#Ab,#gens Ar,#gens Al),ans))))

L={6, 7, 8, 9, 11}
g=#gaps L
elapsedTime mLs=minimalPositionLists(L,g+2,4,Probably=>true,Verbose=>true)-- 297.07s elapsed
#mLs
--alteredVersion
restart
needsPackage "AiWeierstrass"
L={6, 7, 8, 9, 11}
g=#gaps L
elapsedTime mLs=minimalPositionLists(L,g+2,4,Probably=>true,Verbose=>true) -- 283.363s elapsed

L={5, 8, 9, 11, 12}
g=#gaps L
elapsedTime mLs=minimalPositionLists(L,g+2,4,Probably=>true,Verbose=>true)-- 552.477s elapsed
#mLs
elapsedTime tally apply(10,c->testWeierstrass(L,mLs_0))  -- .897438s elapsed
range
///


minimalPositionLists(List) := o-> L -> (
    g:=semigroupGenus L;
    range:=optimalRange(L,g+2,o);
    initList:=prepareInitialPositionList(L,range);
    if o.Verbose then <<"length of the initList = " <<#initList<<flush<<endl;
    I:=semigroupIdeal L;
    (A,runf):=restrictedUnfolding(I,initList);
    (J,family):=getFlatFamily(I,A,runf);
    (J1,family1):=pruneFamily(I,J,family);
    fL:=sort systematicShrinking(L,initList,o);
    --assert(#support J1+#support I== #support family1);
    (B,unfolding):=makeUnfolding L;
    if o.Verbose then (
    <<netList degreeArray(L,positionListToArray(L,
	toList(0..numgens B-1)))<<endl;
    <<netList degreeArray(L,positionListToArray(L,
	initList))<<endl;
    <<netList degreeArray(L,positionListToArray(L,
	fL))<<endl;);
    fL)



/// -- discovery of the non Weierstrass semigroups --with section!

restart
needsPackage "AIWeierstrass"
L={8,10,13,15} --The semigroup L= {8, 10, 13, 15} is probably not a Weierstrass semigroup
g=semigroupGenus L
G=gaps L
elapsedTime tally apply(toList(2..5),i->(#sums(i,G)<=(2*i-1)*(g-1)))
tally apply(toList(2..6),i->((2*i-1)*(g-1)-#sums(i,G)==2*i-3))
--
l=2,n=16*l+19
LKomeda={8,12,8*l+2,8*l+6,n,n+4}
semigroupGenus LKomeda
komeda = (l',n') -> (
    --l' >=0, n'>=0
    l := l'+2;
    n := 16*l+19+2*n';
    {8,12, 8*l+2, 8*l+6, n, n+4}
    )
komeda(0,0)
komedas = (flatten for l' from 0 to 5 list 
           for n' from 0 to 5 list komeda(l',n'));
sort(komedas/semigroupGenus)
netList (komedas/syzFormat)
       -- \textit{J. Komeda}, Commun. Algebra 41, No. 1, 312--324 (2013; Zbl 1270.14014)
fk = res (I = semigroupIdeal komeda(0,0))
sect = trim ideal((fk.dd_5)_{0})
degrees (fk.dd_5)_{0}

isSubset(I, sect)
numgens ring I
fk.dd_4
II = apply(numgens I, j-> ideal(I_*_{0..j}))
II_5
codim I
numgens I
totalBetti  = M -> (
    fM = res M;
    apply(1+length fM, i -> rank fM_i))
netList for j from 5 to 12 list totalBetti II_j
apply(12, j-> isSubset(II_j, sect^2))
--
--elapsedTime b=optimalBound(L,3,Verbose=>true,Probably=>true)   -- 317.658s elapsed
--I=semigroupIdeal(L,BaseField=>ZZ/(nextPrime (10^4+random 10^4)))

(A,unfolding)=makeUnfolding I
numgens A
elapsedTime J=flatteningRelations(I,A,unfolding);-- 29.0817s elapsed
elapsedTime betti(Jt= trim J) -- 24.6694s elapsed
degsA=unique flatten degrees A
posList=prepareInitialPositionList(L,toList(min degsA.. max degsA),Verbose=>true)
elapsedTime (J,family)=getFlatFamily(I,A,unfolding);-- 142.863s elapsed
elapsedTime (J1,family1)=pruneFamily(I,J,family); -- .252741s elapsed

betti J1
#support family1, support family1
betti(fF=res ideal family1)==betti res I

S=ZZ[support family1,Degrees=>apply(support family1,m -> degree m)]
betti(famZZ=sub(fF.dd_1,S))
betti(fF2=sub(fF.dd_2,S))
elapsedTime betti(prod=(famZZ*fF2))
prod==0
betti(fF3=sub(fF.dd_3,S))
betti(prod2=fF2*fF3)
prod2==0
betti(lin=ideal(fF3^{0..3}_{0}))
(famZZ%lin)==0
-- => lin defines a section of the family
lin, numgens lin
betti(fF3modLin=fF3%lin)
-- end leads to nowhere:
betti(nonGorenstein=trim minors(2,fF3modLin))
betti(nG=trim ideal (gens nonGorenstein%lin))
#support nG,#gens S
codim (nGp=sub(nG,ring family1))
betti(fnG=res nGp)
betti(emb=ideal fnG.dd_3)
elapsedTime betti(residual=(nGp:emb))
-- nowhere
betti(fF3modp=sub(fF3modLin,ring family))
betti (transpose  fF3modp)
betti(square=lin^2)
(m1x2=gens trim ideal (famZZ%square));


xs=(support family1)_{0..#L-1}
kk=coefficientRing ring I
A4=kk[xs]
elapsedTime tally apply(100,i->(
	fiber=ideal sub(family1,vars A4|random(kk^1,kk^(#support family1-#L)));
	singFib=ideal singularLocus fiber;
	dim singFib))-- 11.1582s elapsed
elapsedTime  tally apply(50,i->(
	fiber=ideal sub(family1,vars A4|random(kk^1,kk^(#support family1-#L)));
	singFib=ideal singularLocus fiber;
	betti radical singFib)) -- 77.2155s elapsed
-- => very likely always singular, always a single point
--viewHelp coefficients
(M,C)=coefficients family1;
betti M, betti C
coefTally=tally flatten entries sub(C,kk)
apply(keys coefTally,k->sub(k,ZZ))
S=ZZ[support family1,Degrees=>apply(support family1,m -> degree m)]
famZZ=ideal sub(family1,S);
famZZ=sub(family1,S);
elapsedTime betti (syzFam=syz family1)
syzFam^{5}_{3,4}
minimalBetti ideal family1_{0..4}
betti fF
betti (fF.dd_3)
betti(m4x2=fF.dd_3^{4..7}_{1,2})
betti(J=minors(2,m4x2))
betti(m4x1=fF.dd_3^{0..3}_{0})
fourLins=ideal m4x1
rd=random(kk^1,kk^(#support family1-#L))
fib=sub(ideal family1,vars A4|rd)
singFib=ideal singularLocus fib;
radical singFib
sing1=trim sub(fourLins,vars A4|rd)
sing1==radical singFib
betti (square=(fourLins)^2)
betti (twoEqs=trim ideal (family1%square))
-- => only two equations do not vanish quadratically along fourLins
-- => all 4x4 minors of the 4x6 jacobian matrix vanish along fourLins
betti(trim ideal (family1%fourLins))
-- => foutLins is contained in the singular loci of the fiber
betti(m4x2=diff(transpose matrix{xs},gens twoEqs))

betti family1
syzFamZZ=sub(syzFam,S);
famZZ;

prod=(famZZ*syzFamZZ);
prod==0
R=ring family1
-- => flat family over ZZ !

 -- => L is not Weierstrass! 

L={6,8,10,11}
g=semigroupGenus L
elapsedTime minLists=minimalPositionLists(L,g+3,4,Verbose=>true,Probably=>true)
displayMinimalFamilies(apply(minLists,fL->(L,fL)))
------ do not know why the following was done -----
B=value get "ranges9"
netList (Bsorted=sort(B,D->(
    L=D_0;range= D_1;
    posList=prepareInitialPositionList(L,range);
    #posList)))

D=last Bsorted
L=D_0,range=D_1
elapsedTime minLists=minimalPositionLists(L,range,3,Verbose=>true)
netList apply(minLists,finalList->(
        --finalList=minLists_0
	elapsedTime (J,family,runfolding,J1)=showRestrictedFamily(L,finalList);
	netList {{support family}, {J}})
)
    ///

displayMinimalFamilies=method(Options=>{Verbose=>false})
displayMinimalFamilies(List) := o -> (tD -> netList apply (tD, D-> (
	    (J,family,runfolding,J1):=showRestrictedFamily(D_0,D_1);
	    if o.Verbose then <<D_0<<betti J<< betti J1<<endl;
	    netList{{toSequence D_0},{toSequence support family},
		{"degrees of the variables = "|toString flatten (support family/degree)},{J},
	         {"number of eliminated variables from the restricted unfolding is "|toString(#support runfolding-#support family)},
		{transpose family}}
	    )))


 -* returned to AIWeierstrass to NumericalSemigroups*-


buchweitz = i -> (
    --for i>=0 this produces a semigroup B with semigroupGenus 16+i, conductor 26+2i, and
    --#sums(2, gaps buchweitz i) = 3*(semigroupGenus B -1)+1)
    G := toList(1..12+i)| {19+2*i, 21+2*i, 24+2*i, 25+2*i};
    isGapSequence G)


positiveResidue = (p,q) -> if p<0 then p + (1+abs p//q)*q else p%q -- assumes q>0
minimalSemigroupGens=method()
minimalSemigroupGens List := List =>  s ->( --note that minimalSemigroupGens, defined in the system, has options, so the o -> is necessary
    s' := select (s, a -> a != 0);
    g := gcd s';
    if g != 1 then s' = apply(s', a -> a//g);
    m := min s';
    s' = aperySet s';
    out :={};
    for i from 1 to m-1 do
         for j from 1 to m-1 do (
	a := s'_(i-1);
	b := s'_(j-1);
	if a<=b then continue;
	if a-b >= s'_(positiveResidue(i-j-1 , m)) then out = out | {i-1}
	);
    sort ({m}|toList (set s' - set(s'_out)))
     )


isSymmetric = method()
isSymmetric List := Boolean => L -> (
    A := apery L;
    m := A#"multiplicity";
    c := A#"conductor";
    sgrp := #A#"semigroup";
    c == 2*(sgrp - m)
    )

mu = method()
mu List :=List => L -> (
    As := aperySet L;
    m := min L;
    for i from 0 to m-2 list (As_(i) - (i+1))//m
    )
mu HashTable :=List =>  H -> (
    --H should be apery L
    As := aperySet H;
    m := H#"multiplicity";
    for i from 0 to m-2 list (As_(i) - (i+1))//m
    )
semigroupGenus = method()
semigroupGenus List := ZZ => L -> sum mu L
--number of gaps



semigroup = method()
semigroup List := List => L -> (apery L)#"semigroup"


buchweitzCriterion = method()
buchweitzCriterion(List) := L -> (
    G:=gaps L;
    3*(#G-1)-#sums(G,G))

buchweitzCriterion(ZZ,List) := (m,L) -> (
    assert(#L==m-1);
    buchweitzCriterion(prepend(m,L)))


semigroupRing = method(Options => {BaseField => ZZ/nextPrime 10^4,
	                           "VariableName" => getSymbol "x",
			           "MinimalGenerators" => true})
			   
semigroupRing List := Ring => o-> L -> (
    I := semigroupIdeal(L,o);
    R := (ring I)/I;
    R.cache#"sgrp" = L;
    R
    )

weight = method()
weight List := L ->(
    G := sort gaps L;
    sum apply (#G, i -> G_i-1 - i)
    )

semigroupIdeal = method(Options => {BaseField => ZZ/(nextPrime 10^4),
	                           "VariableName" => getSymbol "x",
			           "MinimalGenerators" => true})
semigroupIdeal List := o -> L -> (
    --Here the variables correspond to the given semigroup generators.
    if o#"MinimalGenerators" == true then L':= minimalSemigroupGens L else L' = L;
    m := min L';
    --t := #L;
    x := o#"VariableName";
    kk := o#BaseField;
    R := kk[apply(L',i-> x_(i%m)),Degrees => L'];
    t := symbol t;
    R1 := kk[t];
    I := trim ker map(R1, R, apply(L', i -> t^i));
    I.cache#"sgrp" = L;
    I
        )

apery = method()
apery List := HashTable => L -> (
    --require gcd = 1;
    if gcd L != 1 then error"requires relatively prime generating set";
    A := new MutableHashTable;
    --A will hold the apery set, and a few invariants of the semigroup derived along the way
    m := min L; -- the multiplicity
    a := 0; -- number of keys already filled in A
    S := set L + set{0}; -- S will hold all the semigroup elmeents found, including 0

    --now look for new Apery set elements and semigroup elements until
    --all the keys have been filled.
    s := m;
    while a < m-1 do(
	s = s+1;
	t := any(L, u -> isMember(s-u, S));
	if t then (
	    S = S + set {s};
	    s' := s % m;
	    if not A#?s' and not s'== 0 then (
		A#s' = s;
		a  = a+1)
	    )
	    );

    A#"multiplicity" = m;
    A#"semigroup" = sort toList S;
    A#"conductor" = max A#"semigroup" - m +1;
    hashTable pairs A
    )

aperySet = method()
aperySet HashTable := List => A -> (
    K := select(keys A , k-> class k === ZZ);
    apply(sort K, k -> A#k)
    )
aperySet List := L -> aperySet apery L


    
type = method()
type List := ZZ => L -> #socle L

socle = method()
socle List := List => L' -> (
    L := minimalSemigroupGens L';
    A := apery L;
    K := select(keys A , k-> class k === ZZ);
    aS := apply(sort K, k -> A#k); -- the Apery set
    m := A#"multiplicity";
    select(aS, a -> all(L, ell ->
	            not isMember(a+ell, aS)))
    )

conductor = method()
conductor List :=  L -> (apery L)#"conductor"


def1 = method(Options => {BaseField => ZZ/101,"JustDegs" => true})--, BaseField})
def1 List := o -> L -> (
 --degrees of first-order deformations or the generic first-order deformation itself.
 B := semigroupRing (L, BaseField => o#BaseField);
 I := ideal B;
 S := ring I;
 H := Hom(module I, S^1/I); 
 H' := Hom(S^(-L), S^1/I);
 Dmat := diff( transpose vars S, gens I);
 D := map(S^(-L),module I/I^2, Dmat);
 DI := map(S^(-L),module I, Dmat); 
 t1module := coker map(H,H',Hom(DI, id_(S^1/I))); 
 pt1 := prune t1module;
 pmap := (pt1.cache.pruningMap)^(-1);
 surj := pmap*inducedMap (t1module, H);
 bt1 := basis pt1//surj;
 if o#"JustDegs" == true then return (flatten sort degrees source bt1);
--Default: execution ends here. The rest can be slow, already for multiplicity 5. 

 h := rank source bt1;
 homs := apply(h, i-> homomorphism bt1_{i});
 degs :=  -(homs/degree)|(gens S/degree);
 t := symbol t;
 T := coefficientRing S[t_0..t_(h-1),gens S, Degrees => degs];
 Tbar := T/(ideal(t_0..t_(h-1)))^2;
 II := sub(gens I, Tbar) +sum(h, i-> Tbar_i*(map(Tbar^1, , sub(matrix homs_i, Tbar))));
 ideal(Tbar**II)
 --(h, betti res coker gens I, betti res coker (Tbar** II))
 )

findSemigroups = method()

findSemigroups(ZZ,ZZ,ZZ) := (m,c,g) ->(
ss := findSemigroups(m,g );
select(ss, s -> conductor s == c)
)

findSemigroups (ZZ,ZZ) := (m,g) -> (
     P := compositions (m-1, g-m+1);
     P = apply(P, p -> p+toList(m-1:1));
    for p in P list(
    t := {m}|sort apply(m-1, i-> (i+1+m*p_i));
    if semigroupGenus t != g then continue else minimalSemigroupGens t)
    )

findSemigroups ZZ := g -> (
     flatten for m from 2 to g+1 list(
     P := compositions (m-1, g-m+1);
     P = apply(P, p -> p+toList(m-1:1));
    for p in P list(
    t := {m}|sort apply(m-1, i-> (i+1+m*p_i));
    if semigroupGenus t != g then continue else minimalSemigroupGens t)
    )
)
///
findSemigroups 6
///

gaps = method()
gaps List := L -> (
    --list of gaps in the semigroup generated by L
    A := apery L;
    c := A#"conductor";
    s := A#"semigroup";
    m := min L;
    select(c, i -> not isMember(i, s))
    )

sums = method()
--sums List := L -> sort unique flatten apply(L, i-> apply(L, j-> i+j))
sums (List, List) := (L,L') -> sort unique flatten apply(L, i-> apply(L', j-> i+j))

sums (ZZ,List) := (n,L) ->(
    L' := L;
    for i from 1 to n-1 do (L' = flatten apply(L', j -> apply(L, k -> j+k)));
    sort unique L')

isGapSequence = method()
isGapSequence List := List => G'-> (
    --if the complement in the integers defines a semigroup s then return s; else
    --return false
    G := sort G';
    c := 1+ max G;
    s := select(c+1, i ->i>0 and not isMember(i, G));
    m := min s;
    s = s|apply(m-1,i->c+i+1);
    if G == gaps (L := minimalSemigroupGens s) then L else false
	)



makeUnfolding=method(Options =>
      {Verbose => false,
      BaseField => ZZ/(nextPrime 10^4)})

makeUnfolding Ideal := o-> I ->(
    if not degreeLength ring I == 1 or
       not isHomogeneous I or
       I != trim I then
       error "expected N-graded homogeneous ideal
       given with minimal set of generators";
--    gbI := gb(I,ChangeMatrix =>true);
--    chMat := getChangeMatrix gbI;
    S := ring I;
    kk := coefficientRing S;
    degs := flatten degrees source gens I;
    unfoldingTerms := flatten for i from 0 to max degs-1 list (b:=basis(i,S/I); if b==0 then
	continue else (entries b))_0;
    unfoldingTerms2 := apply(degs,d->select(unfoldingTerms, t-> (degree t)_0 < d));
    a := symbol a;
    avars := flatten apply(#degs,i->apply(#unfoldingTerms2_i,j->a_{i,j}));
    adegs := flatten apply(#degs,i->apply(unfoldingTerms2_i,t->degs_i-(degree t)_0));
    A := kk[avars,Degrees=>adegs];
    avars= reverse sort(gens A,y->degree y);
    adegs=apply(avars,y->(degree y)_0);
    A = kk[avars,Degrees=>adegs];
    SA := kk[gens S|gens A,Degrees=>degrees S|degrees A];
    avars = apply (#degs,i->apply(#unfoldingTerms2_i,j->a_{i,j}));
    unfoldingTerms3 := matrix{apply(#degs,i->sum(#unfoldingTerms2_i,j->
	    sub(a_{i,j},SA)*sub((unfoldingTerms2_i)_j,SA)))}; 
    unfolding := sub(gens I,SA)+unfoldingTerms3;
    (A,unfolding)
    )

makeUnfolding List := o-> L -> (
        I:= trim ideal semigroupRing(L,BaseField=>o#BaseField);
	makeUnfolding I)

flatteningRelations=method()
flatteningRelations(Ideal,Ring, Matrix) := (I,A,unfolding) -> (
    gbI:=gb(I,ChangeMatrix=>true);
    S := ring I;
    SA := ring unfolding;
    chMat:=getChangeMatrix gbI;
    unfoldingGB := unfolding*sub(chMat,SA);
    -- can one use the build in gb algorithm to compute the
    -- flattening relations faster
    unfGBf:=forceGB unfoldingGB;
    ldT := flatten entries leadTerm unfoldingGB;
    s0:=syz sub(gens gbI,SA);
    testSyzygy1:=unfoldingGB*s0;
    testSyzygy2:=testSyzygy1%unfGBf;
    u1:=null;
    ma := max flatten degrees source syz leadTerm gens gbI;
    rems := reverse flatten for i from 0 to ma list (b:=basis(i,S^1/I); if b==0 then  continue else (entries b))_0;
    us := apply(rems,u->(u1=contract(sub(u,SA),testSyzygy2);testSyzygy2-sub(u,SA)*u1;
	u1));
    relsA:=sub(ideal(flatten us),A);
    relsA
     )



ewt=method()
ewt(List):= L -> (
    G:=gaps L;
    L1:=minimalSemigroupGens L;
    sum(L1,a->#select(G,b->a<b))
    )

effectiveWeight = method()
effectiveWeight List := sgrp -> ewt sgrp

findPoint = method(Options => {Verbose => false})--,"IgnoreGrading" => true })
-- this assumes that
-- c == sub(ideal prune(ring c/c), ring c))
findPoint(Ideal) := o -> (J) -> (
    --need to be revisited, looks differnt than the corrected versions below
    c:= radical J;
    if degree c =!=degree J then
    <<"taking radicals makes a difference in findPoints"<<flush <<endl;
    S := ring c;
    kk := coefficientRing S;
    rc:=radical c;
    c1 := prune rc;  
    R := ring c;
    A1 := vars R % rc;
    if c1==0 then(
	point := sub(A1,random(R^1,R^(numgens R)));
	assert(sub(c, point) == 0);
	return sub(point,kk);
	);
    if o.Verbose then << "has to solve" <<flush<< endl;

    R1 := kk[gens ring c1];
    cR1 := radical sub(c1, R1);
    p := null;count := 2;
    if o.Verbose then (
    
    elapsedTime while (count < 10 and (
	p = first randomPoints(count,cR1,BruteForceAttempts => 0);
	if p == {} then
            (<< "No point was found by randomPoints"<<endl; return null);
        product flatten p ==0)) do (count = count+1);
        if count == 10 then return null

    ) else (

    while (count < 10 and (
	p = first randomPoints(count,cR1,BruteForceAttempts => 0); --maybe 20 should be replaced by count
	product flatten p ==0)) do(count = count+1);
    if count == 10 then return null
    );

    if p == {} then
    (<< "No point was found by randomPoints"<<endl; return null);

    point = sub(matrix{ p},kk);

    assert(sub(cR1, point) == 0);
    keyVars := apply(gens R1, x -> sub (x,S));
    subList := apply(#keyVars, i -> (keyVars_i => point_(0,i)));
    point1 := sub(sub(A1, subList), kk);
    assert(sub(c, point1) == 0);
return point1
)

findPoint(Ideal,Number,Number) := o -> (J,a,b) -> ( -- a seems not to be used
    c:= radical J;
    if degree c =!=degree J then
    <<"taking radicals makes a difference in findPoints"<<flush <<endl;
    S := ring c;
    kk := coefficientRing S;
    rc:=radical c;
    c1 := prune rc;  
    R := ring c;
    A1 := vars R % rc;
    if c1==0 then(
	point := sub(A1,random(R^1,R^(numgens R)));
	assert(sub(c, point) == 0);
	return sub(point,kk);
	);
    if o.Verbose then << "has to solve" <<flush<< endl;

    R1 := kk[gens ring c1];
    cR1 := radical sub(c1, R1);
    p := {}; numberOfPoints := 1;
    if o.Verbose then (
	elapsedTime while (numberOfPoints < b and (
	   p = randomPoints(numberOfPoints,cR1,BruteForceAttempts => 0); 
	   p == {} or product first p ==0)) do (numberOfPoints = numberOfPoints+1);
        if numberOfPoints == b then(
           (<< "No point was found by randomPoints"<<endl; return null);
           return null);
    ) else (

    while (numberOfPoints < b and (
	p = randomPoints(numberOfPoints,cR1,BruteForceAttempts => 0); 
	p == {} or product first p ==0)) do (numberOfPoints = numberOfPoints+1);
    if numberOfPoints == b then return null;

    );

    point = sub(matrix{first p},kk);

    assert(sub(cR1, point) == 0);
    keyVars := apply(gens R1, x -> sub (x,S));
    subList := apply(#keyVars, i -> (keyVars_i => point_(0,i)));
    point1 := sub(sub(A1, subList), kk);
    assert(sub(c, point1) == 0);
return point1
)



knownExample=method()
knownExample(List) := L-> (
    if #L<=3 then return true;--determinantal
    if #L == 4 and type L == 1 then return true;--pfaffian
    --if L is a generalized Arithmeti cProgression L
    --then in some cases the paper of Oneto and Tamone shows smoothness
    --if min L < 6 then return true; -- see Komeda xxx
    g := semigroupGenus L;
    if ewt L < g or min L <5 then return true else false)

buchweitzSemigroups = method()
buchweitzSemigroups (ZZ, ZZ, ZZ) := (m,c,g) ->(
      LL := findSemigroups(m,c,g);
      if #LL !=0 then (
        LB := select(LL, L -> (
	   G := gaps L;
	   #sums(G,G) > 3*(#G -1)));
           --if #LB >0 then 
	   --     (<<LB<<endl<<flush);
	   LB) else {}
      )
  
buchweitzSemigroups (ZZ, ZZ) := (m,g) ->(
      LL := findSemigroups(m,g);
      if #LL !=0 then (
        LB := select(LL, L -> (
	   G := gaps L;
	   #sums(G,G) > 3*(#G -1)));
           --if #LB >0 then 
	   --     (<<LB<<endl<<flush);
	   LB) else {}
      )

  buchweitzSemigroups ZZ := g ->(
      LL := findSemigroups g;
      if #LL !=0 then (
        LB := select(LL, L -> (
	   G := gaps L;
	   #sums(G,G) > 3*(#G -1)));
           --if #LB >0 then 
	   --     (<<LB<<endl<<flush);
	   LB) else {}
      )

getFlatFamily=method(Options =>
      {Verbose => false,
      BaseField => ZZ/(nextPrime 10^4)})


getFlatFamily(Ideal,Ring,Matrix,List) :=  o -> (I,A,unfolding,restrictionList) -> (
    --Input: I, the ideal of the semigroup
    --       A coordinate ring of 
    --       unfolding, a matrix defining a family over kk[gens ring I|gens A]
    --       restrictionList, aList of variables 
    --Output: I, the ideal of the semigroup
    --        J1 the ideal of the flattening relations in A
    --        family the ideal in  SA defining
    --        the flat family over (Spec A/J1)
    SA:=ring unfolding;
    S:= ring I;
    --restrictionList
    runfolding:=unfolding%sub(ideal (vars A%sub(ideal restrictionList,A)),SA);
    if o.Verbose then (
	 <<"flatteningRelations"<<endl<<flush;
          elapsedTime J:=flatteningRelations(I,A,runfolding);
	  ) else (
	 J=flatteningRelations(I,A,runfolding)
	 );
    mA:= max flatten degrees A;
    if o.Verbose then (
	<<"next gb" << endl<<flush;
	elapsedTime gbJ:=forceGB gens gb(J,DegreeLimit=>mA);) else (
	gbJ=forceGB gens gb(J,DegreeLimit=>mA););
    varsAmodJ:=vars A%gbJ;
    J1:=sub(J,varsAmodJ);    
    family:=sub(runfolding,sub(vars S,SA)|sub(varsAmodJ,SA));
    if J1==0 then assert (betti syz family==betti syz gens I);
    (J1,family))



getFlatFamily(Ideal,Ring,Matrix) := o ->(I,A,runfolding) -> (
    --Input: I, the ideal of the semigroup
    --       A coordinate ring of 
    --       a matrix defining a family over kk[gens ring I|gens A]
    --Output: I, the ideal of the semigroup
    --        J1 the ideal of the flattening relations in A
    --        family the ideal in  SA defining
    --        the flat family over (Spec A/J1)
    assert(#gens ring runfolding==#gens A + #gens ring I);
    SA:=ring runfolding;
    S:= ring I;
    if o.Verbose then (
	 <<"flatteningRelations"<<endl<<flush;
          elapsedTime J:=flatteningRelations(I,A,runfolding);
	  ) else (
	 J=flatteningRelations(I,A,runfolding)
	 );
    mA:= max flatten degrees A;
    gbJ:=null;
    if o.Verbose then (
	<<"next gb" << endl<<flush;
	elapsedTime gbJ=forceGB gens gb(J,DegreeLimit=>mA);) else (
	gbJ=forceGB gens gb(J,DegreeLimit=>mA););
    varsAmodJ:=(matrix{support runfolding})%sub(gens gbJ,SA);
    J1:=trim sub(J,((sub(varsAmodJ,ring J))_{#gens S..#gens SA-1}));-- to be corrected   
    family:=sub(runfolding,sub(varsAmodJ,SA));
    if J1==0 then assert (betti syz family==betti syz gens I);
    (J1,family))

-* End returned to AIW*-




pruneFamily=method(Options=>{Verbose=>false})
pruneFamily(Ideal,Ideal,Matrix) := o -> (I,J,family) ->(
    -- Input: I, the ideal of the semigroup
    --       J ideal of flattening relations
    --       a matrix defining a family over kk[gens ring I|gens ring J]
    -- Output: J1 pruned flattening relations     
    --        family1 pruned family
    S:=ring I;
    kk:=coefficientRing S;
    SA:=kk[support family,Degrees=>apply(support family, m->degree m)];
    family1:=sub(family,SA);
    as:=drop(support family,numgens S);
    A:=kk[as,Degrees=>apply(as,m->degree m)];
    J1:=if o.Verbose then (<<"time for prune J = " <<flush<<endl;
	elapsedTime prune trim sub(J,A)) else (prune trim sub(J,A));
    if J1 == 0 or
     sub(gens J1,A)%(ideal gens A)^2== 0 then
     family2:=family1 else (
	if o.Verbose then (<<"time to reduce family1= "<<flush<<endl;
	    elapsedTime family2=family1%sub(J1,SA)) else (family2=family1%sub(J1,SA)));

    SA':=kk[support family2,Degrees=>apply(support family2, m->degree m)];   
    family3:=sub(family2,SA');
    as=drop(support family3,numgens S);
    A=kk[as,Degrees=>apply(as,m->degree m)];
    --assert(#support J1+#support I==#support family 3);
    J3:=prune trim sub(J1,A);
    (J3,family3)
    )
///
     L={6, 8, 10, 11, 13}
     I=ideal semigroupRing(L,BaseField=>ZZ/nextPrime 10^4);
     (A,unfolding)=makeUnfolding I;
     b = semigroupGenus L-3; 
     as=apply(numgens I,i->a=drop(support unfolding_{i},#L));
     rL=apply(#as,i->select(as_i,m->(degree m)_0> b));
     restrictionList=apply(flatten rL,m->sub(m,A));
     (J,family)=getFlatFamily(I,A,unfolding,restrictionList);
     (J2,family2)=pruneFamily(I,J,family);
     cJ=decompose J2

     assert(#cJ == 2)
     apply(cJ, J -> betti J)
     apply(cJ,J->withRandomPoint(I,J,family2))

     assert(withComponents(I,cJ, family2) == -1)
     withComponents(I,cJ, family2)
///

-* is this used ?*-
randomFiber=method() 
randomFiber(Ideal,Ideal,Matrix) := (I,J,family) -> (
    if #support J== 0 then (
	S:= ring I;
	kk:=coefficientRing S;
	SA:=kk[support family,Degrees=>apply(support family, m->degree m)];
	r:= #gens SA-#gens S;
	randomPoint := random(kk^1,kk^r);
	fiber:=ideal sub(sub(family,SA),vars S|randomPoint));
	return fiber)


checkFlatness =method(Options=>{Verbose=>false})
checkFlatness(Ideal,Ideal) := o -> (I,fib) -> (
      -- Input: I, Ideal of a semigroup ring
      --       fiber, ideal of a random fiber in a one parameter family
      -- Output: Boolean,
      --         the homogenized family is flat 
        S:= ring I;
	kk:=coefficientRing S;
        t:=symbol t;
	St:= kk[gens S|{t},Degrees=>apply(gens S,m->(degree m)_0)|{1}];
	fibt:=homogenize(sub(fib,St),t);
	betti res(I,LengthLimit=>2)==betti res(fibt,LengthLimit=>2)
	)

withAffineBase=method(Options=>{Verbose=>false,Probably=>false})
withAffineBase(Ideal,Ideal,Matrix) := o -> (I,J,family) -> (
    -- Input: I, the ideal of the semigroup
    --        J ideal of flattening relations assumed to be zero -- silly
    --        a matrix defining a family over kk[gens ring I|gens ring J]
    -- Output: dimension of the singulocus of a random fiber               
	S:= ring I;
	kk:=coefficientRing S;
	SA:=kk[support family,Degrees=>apply(support family, m->degree m)];
	r:= #gens SA-#gens S;
	randomPoint := random(kk^1,kk^r);
	fiber := ideal sub(sub(family,SA),vars S|randomPoint);
	assert( dim fiber ==1);
	assert(checkFlatness(I,fiber));
	if not o.Probably then return dim singularLocus fiber else
	dimSingularLocusOfFiber(fiber,Probably=>o.Probably)
	)

dimSingularLocusOfFiber=method(Options=>{Probably=>false})
dimSingularLocusOfFiber(Ideal) := o -> fiber ->(
    if not o.Probably then return dim singularLocus fiber;
    probAnswer:=regularInCodimension(1, ring fiber/fiber);
    if class probAnswer === Boolean then return -1;   
    if probAnswer == null then return 0)
///
fiber
dimSingularLocusOfFiber(fiber,Probably=>false)
dimSingularLocusOfFiber(fiber,Probably=>true)
viewHelp regularInCodimension
CodimCheckFunction => 3
PairLimit => 10

L={6, 8, 10, 11, 13}
elapsedTime optimalBound(L,Probably=>false,Verbose=>true)  -- 7.47991s elapsed
elapsedTime optimalBound(L,Probably=>true,Verbose=>true)  -- 37.5688s elapsed
///
	
withAffineBase(Ideal,Matrix) := o ->  (I,family) -> (
    -- Input: I, the ideal of the semigroup      
    --        a matrix defining a family over kk[gens ring I|gens ring J]
    -- Output: dimension of the singulocus of a random fiber               
	S:= ring I;
	kk:=coefficientRing S;
	SA:=kk[support family,Degrees=>apply(support family, m->degree m)];
	r:= #gens SA-#gens S;
	randomPoint := random(kk^1,kk^r);
	fiber := ideal sub(sub(family,SA),vars S|randomPoint);
        assert(checkFlatness(I,fiber));
	assert( dim fiber ==1);	
	dim singularLocus fiber)
 

    

testWeierstrass=method(Options=>{Verbose=>false,Probably=>true})

testWeierstrass(List,ZZ) := o -> (L,bound) -> (
    I:=ideal semigroupRing(L,BaseField=>ZZ/nextPrime 10^4);
    (A,unfolding) := makeUnfolding I;
    xs:=(support unfolding)_{0..#L-1};
    as := apply(numgens I,i-> select(support unfolding_{i},m->not member(m,xs)));
    if o.Verbose then (<<"degrees of the variables in the universal unfolding:"<< endl;
	<<netList apply(numgens I,i->apply(as_i, m->(degree m)_0)) << endl);
    rL := apply(#as,i->select(as_i,m->(degree m)_0> bound));
    if o.Verbose then
    (<<"degrees of the variables after restriction"<<endl;
	<<netList apply(#rL,i->apply(rL_i,m->(degree m)_0))<<endl;);
    restrictionList := apply(flatten rL,m->sub(m,A));
    (J,family) := getFlatFamily(I,A,unfolding,restrictionList);
    (J1,family1) := pruneFamily(I,J,family);
    if J1 == 0 then (
	    fib := randomFiber(I,J1,family1);
	    dimSingularLocusOfFiber(fib,Probably=>o.Probably)); 	
    if o.Verbose then (); --altered
    if o.Verbose then	(<<" time to decompose the base = "<<endl;
	    elapsedTime cJ := decompose J1;) else cJ=decompose J1;
    if #cJ == 1 then(
	wrp := withRandomPoint(I,first cJ,family1,o);
	    if class wrp === Nothing then return null;
	    return wrp);
    if o.Verbose then <<"number of components = " <<#cJ <<flush<<endl;
    withComponents(I,cJ,family1,o)
    )


testWeierstrass(List,List):= o -> (L,smallerList) -> (
--  Input L, List
--            generators of a semigroup
--         smallerList, List
--         positions of the variables in the unfolding will be used
    I:=ideal semigroupRing(L,BaseField=>ZZ/nextPrime 10^4);
    (A,unfolding):=makeUnfolding(I);
    xs:=(support unfolding)_{0..#L-1};
    as := apply(numgens I,i-> select(support unfolding_{i},m->not member(m,xs)));
    restrictionList:=(apply(flatten as,m->sub(m,A)))_smallerList;
--    restrictionList
    (J,family) := getFlatFamily(I,A,unfolding,restrictionList);
    (J1,family1) := pruneFamily(I,J,family);
    --J1, J, J1==0
    --transpose family
    if J1 == 0 then (
	    fib := randomFiber(I,J1,family1);
    --	    fib
--	    withAffineBase(I,J1,family1)
--	    withRandomPoint(I,J1,family1)
--	    dim singularLocus fib
	    return dim singularLocus fib); 	
    if o.Verbose then
	(<<" time to decompose the base = "<<endl;
	    elapsedTime cJ := decompose J1) else cJ=decompose J1;
    if #cJ == 1 then(
	wrp := withRandomPoint(I,first cJ,family1,o);
	if class wrp === Nothing then return null;
        wrp) else
    withComponents(I,cJ,family1,o)
    )
-*
testWeierstrass(List,ZZ) := o -> (L,bound) -> (
    I:=ideal semigroupRing(L,BaseField=>ZZ/nextPrime 10^4);
    (A,unfolding) := makeUnfolding I;
    xs:=(support unfolding)_{0..#L-1};
    as := apply(numgens I,i-> select(support unfolding_{i},m->not member(m,xs)));
    if o.Verbose then (<<"degrees of the variables in the universal unfolding:"<< endl;
	<<netList apply(numgens I,i->apply(as_i, m->(degree m)_0)) << endl);
    rL := apply(#as,i->select(as_i,m->(degree m)_0> bound));
    if o.Verbose then
    (<<"degrees of the variables after restriction"<<endl;
	<<netList apply(#rL,i->apply(rL_i,m->(degree m)_0))<<endl;);
    restrictionList := apply(flatten rL,m->sub(m,A));
    (J,family) := getFlatFamily(I,A,unfolding,restrictionList);
    (J1,family1) := pruneFamily(I,J,family);
    if J1 == 0 then (
	    fib := randomFiber(I,J1,family1);
	    dimSingularLocusOfFiber(fib,Probably=>o.Probably)); 	
    if o.Verbose then (); --altered
    if o.Verbose then	(<<" time to decompose the base = "<<endl;
	    elapsedTime cJ := decompose J1;) else cJ=decompose J1;
    if #cJ == 1 then(
	wrp := withRandomPoint(I,first cJ,family1,o);
	    if class wrp === Nothing then return null;
	    return wrp);
    if o.Verbose then <<"number of components = " <<#cJ <<flush<<endl;
    withComponents(I,cJ,family1,o)
    )
*-


testWeierstrassRange = method(Options=>{Verbose=>false,Probably=>true})
testWeierstrassRange(List,List):= o -> (L,range) -> (
--  Input L, List
--         input list: range of degrees
--         output: 0 or -1 (smoothness of fiber in the range)
    I:=ideal semigroupRing(L,BaseField=>ZZ/nextPrime 10^4);
    (A,unfolding):=makeUnfolding(I);
    xs:=(support unfolding)_{0..#L-1};
    as := apply(numgens I,i-> select(support unfolding_{i},m->not member(m,xs)));
    restrictionList:=
        select(flatten as, m->member((degree m)_0, range));
--    restrictionList:=(apply(flatten as,m->sub(m,A)))_smallerList;
--    restrictionList
    (J,family) := getFlatFamily(I,A,unfolding,restrictionList);
    (J1,family1) := pruneFamily(I,J,family);--,Verbose=>o.Verbose);
    --J1, J, J1==0
    --transpose family
    if o.Verbose then <<"number of relations = " <<numgens J1<<flush<<endl;
    if J1 == 0 then (
	    fib := randomFiber(I,J1,family1);
    --	    fib
--	    withAffineBase(I,J1,family1)
--	    withRandomPoint(I,J1,family1)
--	    dim singularLocus fib
	    dimSingularLocusOfFiber(fib,Probably=>true)
	    ); 	
    if o.Verbose then
	(<<" time to decompose the base = "<<flush<<endl;
	    elapsedTime cJ := decompose J1) else cJ=decompose J1;
    
    if #cJ == 1 then (
	if o.Verbose then (elapsedTime
	ans := withRandomPoint(I,J1,family1,Probably=>o.Probably)) else (
	ans = withRandomPoint(I,J1,family1,Probably=>o.Probably));
        if class ans === Nothing then return null else
    return ans);

    assert(#cJ >1);

    if o.Verbose then (" <<number of components = "<< #cJ<<flush<<endl;
      elapsedTime ans = withComponents(I,cJ,family1,Probably=>o.Probably))
      else (ans = withComponents(I,cJ,family1,Probably=>o.Probably));
        if class ans === Nothing then return null;
    return ans;
    )

optimalRange=method(Options=>{Verbose=>false,Probably=>true,Bisection=>false})
optimalRange(List,ZZ) := o -> (L,guess) -> (
    b:=if o.Verbose then elapsedTime optimalBound(L,guess,Probably=> o.Probably, Verbose=>o.Verbose) else (
	optimalBound(L,guess,Probably=> o.Probably));
    if o.Verbose then <<"optimal lower bound = " <<b <<endl;
    a:= b+1;
    if not o.Bisection then (
    range:=null;
    while(range = toList(b+1..a);
	tWR := testWeierstrassRange(
	    L,range,Probably=>o.Probably);
	if class tWR === Nothing then return null;
	tWR == 0) do (
	a=a+1;
	if o.Verbose then << "testing range = "<< range <<endl);
    return range) else (
    I:= semigroupIdeal L;
    b1:=(max degrees source gens I)_0;
    a1:=b+1; c:=null;
    while (b1>a1+1) do (
	c = floor ((b1+a1)/2);
	if o.Verbose then <<"midpoint = " <<c<<flush<<endl;
	if testWeierstrassRange(L,toList(a..c),Verbose=>o.Verbose)==-1 then ( b1=c) else (
	a1=c));
    
    if a1==b1 then return toList(a..a1);
    assert(b1==a1+1);
    if testWeierstrassRange(L,toList(a..a1),Verbose=>o.Verbose)==-1 then return toList(a..a1);
    assert(testWeierstrassRange(L,toList(a..b1))==-1);
    return toList(a..b1))
)


	    

/// -* Test bisection *-
L={6,7,8,10}
g=#gaps L
b=optimalBound(L,g)

///
    

testWeierstrass(Ideal,Ring,Matrix) := o -> (I,A,runfolding) -> (
    (J,family) := getFlatFamily(I,A,runfolding);
    (J1,family1) := pruneFamily(I,J,family);
    if
    numgens J1 == 0
    then (
	if o.Verbose and  #support family1== #support I then
	 print " not enough variables ";
	withAffineBase(I,family1) )
    else (	
	if o.Verbose then
	(<<" time to decompose the base = "<<endl;
	    elapsedTime cJ := decompose J1
	    )
	else cJ=decompose J1;
    withComponents(I,cJ,family1,Probably=>o.Probably)
    )
)



restrictedUnfolding = method() -- to be improved
restrictedUnfolding(Ideal,List) := (I,positionList) -> (
    S := ring I;
    (A,unfolding) := makeUnfolding I;
    kk := coefficientRing A;
    listInA:=(gens A)_positionList;   
    sub1 := matrix{apply(numgens A,i->if member(i,positionList) then (gens A)_i else 0)};
    A' :=  kk[support sub1,Degrees=>apply(support sub1,m->(degree m)_0)];    
    SA' := kk[gens S|gens A',Degrees=>apply((gens ring I|gens A'),m->(degree m)_0)];
    runfolding := sub(unfolding,sub(vars S,SA')|sub(sub1,SA'));
    (A',runfolding)
    )
 
optimalBound=method(Options=>{Verbose=>false,Probably=>true})

-- The optimal bound is defined to be the smallest nonnegative integer such that
-- testWeierstrass (L,b) returns -1 meaning that it has found a smoothing using
-- monomials of the unfolding whose degrees are > b.

optimalBound(List) := o -> L -> (
    I:=ideal semigroupRing L;
    b:=max flatten flatten degrees source gens I-1;

    while (tw := testWeierstrass(L,b,Probably=>o.Probably);
	if class tw === Nothing then (break; return null);
	b>0 and tw == 0) do (b=b-1;
	if o.Verbose then <<b<<endl;);
   if b == 0 then print (L, " may not be Weierstrass");
    b)
optimalBound(List,ZZ) := o -> (L,guess) -> (
    b := guess;
    while 
    (tw := testWeierstrass(L,b,o);
	if class tw === Nothing then (break; return null);
	b>-1 and tw==0) do
    (b=b-1;
	if o.Verbose then print b);
    if b==-1 then (<<"The semigroup L= "<<L<<" is probably not a Weierstrass semigroup"<<endl;
	return b);

    tw = testWeierstrass(L,b,o);
	if class tw === Nothing then return null;
    if tw ==-1 then (
	while(
	    tw = testWeierstrass(L,b,Probably=>o.Probably);
	if class tw === Nothing then (break; return null);
        tw ==-1) do (
	    b=b+1;
	    if o.Verbose then << "testing b = " <<b<<endl;);
	return b-1);
    b)
///
restart
needsPackage "AIWeierstrass"
L = {5,6,7}
g=semigroupGenus L
b=optimalBound(L,2*g+4,Verbose=>true, Probably=>true)
testWeierstrass(L,b+1,Probably=>true)==0
testWeierstrass(L,b,Probably=>true)==-1
b=optimalBound(L,g,Verbose=>true, Probably=>true)
testWeierstrass(L,b+1,Probably=>true)==0
testWeierstrass(L,b,Probably=>true)==-1
///
prepareInitialPositionList=method(Options=>{Verbose=>false,Probably=>true})


prepareInitialPositionList(List) := o -> L -> (
    I := ideal semigroupRing(L,BaseField=>ZZ/nextPrime 10^4);
    (A,unfolding) := makeUnfolding(I);
    xs:=(support unfolding)_{0..#L-1};
    as := apply(numgens I,i-> select(support unfolding_{i},m->not member(m,xs)));
    --(as := apply(numgens I,i-> drop(support unfolding_{i},#L)));
    if o.Verbose then (<<"degrees of the variables in the universal unfolding:"<< endl;
	<<netList apply(numgens I,i->apply(as_i, m->(degree m)_0)) << endl);
    optBound := optimalBound(L,Verbose=>o.Verbose,Probably=>o.Probably);
    rL := apply(#as,i->select(as_i,m->(degree m)_0> optBound));
    if o.Verbose then (<<"degrees of the variables after restriction"<<endl;
	<<netList apply(#rL,i->apply(rL_i,m->(degree m)_0))<<endl);
    positionList:=apply(flatten rL,m->position(flatten as, n-> m==n));
    positionList)

prepareInitialPositionList(List,ZZ) := o -> (L,b) -> (
    I := ideal semigroupRing(L,BaseField=>ZZ/nextPrime 10^4);
    (A,unfolding) := makeUnfolding(I);
    xs:=(support unfolding)_{0..#L-1};
    as := apply(numgens I,i-> select(support unfolding_{i},m->not member(m,xs)));
    --(as := apply(numgens I,i-> drop(support unfolding_{i},#L)));
    if o.Verbose then (<<"degrees of the variables in the universal unfolding:"<< endl;
	<<netList apply(numgens I,i->apply(as_i, m->(degree m)_0)) << endl);
    --optBound := optimalBound(L,Verbose=>o.Verbose,Probably=>o.Probably);
    rL := apply(#as,i->select(as_i,m->(degree m)_0> b));
    if o.Verbose then (<<"degrees of the variables after restriction"<<endl;
	<<netList apply(#rL,i->apply(rL_i,m->(degree m)_0))<<endl);
    positionList:=apply(flatten rL,m->position(flatten as, n-> m==n));
    positionList)

prepareInitialPositionList(List,List) := o ->
    (L,range) -> (
    I := ideal semigroupRing(L,BaseField=>ZZ/nextPrime 10^4);
    (A,unfolding) := makeUnfolding(I);
    xs:=(support unfolding)_{0..#L-1};
    as := apply(numgens I,i-> select(support unfolding_{i},m->not member(m,xs)));
    as1:= flatten as;
    --(as := apply(numgens I,i-> drop(support unfolding_{i},#L)));
    if o.Verbose then (<<"degrees of the variables in the universal unfolding:"<< endl;
	<<netList apply(numgens I,i->apply(as_i, m->(degree m)_0)) << endl;
	);
    --optBound := optimalBound(L,Verbose=>o.Verbose,Probably=>o.Probably);   
    rL :=  if #flatten range == #range then (select(as1,m->member((degree m)_0,range))
	) else (
	assert(#range==numgens I);
	flatten apply(numgens I,i->select(as_i,m->member((degree m)_0,range_i))));	    
    positionList:=apply(flatten rL,m->position(as1, n-> m==n));
    if o.Verbose then (<<"degrees of the variables after restriction"<<endl;
	<<netList degreeArray(L,positionListToArray(L,positionList))<<endl);
    positionList)


positionListToArray=method(Options=>{Verbose=>false})
positionListToArray(List,List):= o -> (L,positionList) -> (
    I := ideal semigroupRing(L,BaseField=>ZZ/nextPrime 10^4);
    (A,unfolding) := makeUnfolding(I);
    xs:=(support unfolding)_{0..#L-1};
    as := apply(numgens I,i-> select(support unfolding_{i},m->not member(m,xs)));

    arrayBoundaries:= apply(numgens I+1,i->sum(i,j->#as_j));
    positionArray:=apply(numgens I,i->select(positionList,j->(arrayBoundaries_i<=j and
		j < arrayBoundaries_(i+1))));
    if o.Verbose then (<<"positionArray = "<< endl;
	<<netList apply(numgens I,i->positionArray_i) << endl;);
    positionArray
    )

positionArrayToList=method()
positionArrayToList(List):= positionArray -> flatten positionArray


degreeArray=method()
degreeArray(List,List) := (L,positionArray) -> (
     I := ideal semigroupRing(L,BaseField=>ZZ/nextPrime 10^4);
     (A,unfolding) := makeUnfolding(I);
     xs:=(support unfolding)_{0..#L-1};
     as := apply(numgens I,i-> select(support unfolding_{i},m->not member(m,xs)));
     apply(numgens I,i->apply(positionArray_i,j->(degree (flatten as)_j)_0))
     )
     

showRestrictedFamily=method()
showRestrictedFamily(List,List) := (L,leftPositions) -> (
    I := ideal semigroupRing(L,BaseField=>ZZ/nextPrime 10^4);
    (A,unfolding) := makeUnfolding(I);
    xs:=(support unfolding)_{0..#L-1};
    as := apply(numgens I,i-> select(support unfolding_{i},m->not member(m,xs)));
    as1 := flatten as;
    --(as := apply(numgens I,i-> drop(support unfolding_{i},#L))); --perhaps has to be corrected
    restrictionList := apply((flatten as)_leftPositions,m->sub(m,A));
    superflousVars:=ideal(vars A%ideal restrictionList);
    runfolding:= unfolding%sub(ideal superflousVars,ring unfolding);
    kk:=coefficientRing ring I;
    SB:=kk[support runfolding,Degrees=>apply(support runfolding,m->degree m)];
    runfolding = sub(runfolding,SB);
    --(B1,runfolding1):=restrictedUnfolding(I,leftPositions)
    (J,family) := getFlatFamily(I,A,unfolding,restrictionList);
    (J1,family1) := pruneFamily(I,J,family);
    bs:=(entries((vars SB)_{#L..numgens SB-1}))_0;
    B:=kk[bs,Degrees=>apply(bs,m->degree m)];
    J2:=trim flatteningRelations(I,B,runfolding);
    (J1,family1,runfolding,J2))

systematicShrinking=method(Options=>{Verbose=>false,Probably=>true})
systematicShrinking(List,List) := o -> (L,initialList) -> (
    I:=ideal semigroupRing L;
    (A,unfolding) := makeUnfolding I;
    xs:=(support unfolding)_{0..#L-1};
    as := apply(numgens I,i-> select(support unfolding_{i},m->not member(m,xs)));
    as1 := flatten as;
    smallerList := initialList;
    success:= false; testList:=null;remPos:=null;j:=null;
    while ( success=false;
      for i from 0 to #smallerList-1 do (
	testList=delete(smallerList_i, smallerList);
	if o.Verbose then (
	    elapsedTime tW := testWeierstrass(L,testList,o)) else (
	tW = testWeierstrass(L,testList,o));
	if o.Verbose then <<"tW = "<<tW<<endl<<flush;
	
	if class tW === Nothing then continue;--b return null;
	if tW == -1 then
	     (remPos=smallerList_i;
	      success=true;	      
	      break) else continue);
	success) do (
	   if o.Verbose then <<as1_remPos<<degree as1_remPos<<endl;
	   --smallerList=select(smallerList,i->not i==remPos)
	   j=position(smallerList,i->i==remPos);
	   smallerList=smallerList_{j+1..#smallerList-1}|smallerList_{0..j-1}
	   );
       smallerList)
///
L={5,9,13}	 
optBound=optimalBound L 
initialList=prepareInitialPositionList(L,optBound,Verbose=>true)
finalList=systematicShrinking(L,initialList,Verbose=>true)
--leftPositions=finalList
(J,family,runfolding,J1)=showRestrictedFamily(L,finalList); 
J, J1
transpose runfolding
transpose family
support family
support runfolding
///

shrinkRange=method(Options=>{Verbose=>false})

shrinkRange(List,List) := o -> (L,range) -> (
    newRange := range;
    testDegrees:=drop(drop(range,-1),1);
    d:=null;
    while #testDegrees >0 do (
	d=first testDegrees;
	testDegrees=delete(d,testDegrees);
	if testWeierstrassRange(L,delete(d,newRange))==-1 then newRange=delete(d,newRange));
    newRange)

/// -* [ shrinkRange ] *-
ls()
tD=flatten getFromDisk "tD5new"
netList apply(tD,D->(L=D_0,mL=D_1;
	(L,sort unique flatten degreeArray(L,positionListToArray(L,mL)))))
L={4, 6, 9, 11}; range=toList(8..14)
elapsedTime newRange=shrinkRange(L,range) -- 12.8783s elapsed
elapsedTime minLists=minimalPositionLists(L,newRange,2) -- 56.6298s elapsed togther about 69 secs
elapsedTime minLists=minimalPositionLists(L,range,2) -- 150.922s elapsed
///


/// -* showRestrictedFamily *-
L={5,9,13}

I=ideal semigroupRing L
optBound=optimalBound L 
initialList=prepareInitialPositionList(L,Verbose=>true)
finalList=systematicShrinking(L,initialList,Verbose=>true)
(J,family,runfolding,J1)=showRestrictedFamily(L,finalList); 
SB= ring runfolding
assert(sub(family,SB)==(runfolding%sub(J1,SB)))
J, J1
transpose family ,transpose runfolding
///

getFiber=method(Options=>{Verbose=>false})
getFiber(List,ZZ) := o -> (L,bound) -> (
    I:=ideal semigroupRing(L,BaseField=>ZZ/nextPrime 10^4);
    (A,unfolding) := makeUnfolding I;
    xs:=(support unfolding)_{0..#L-1};
    as := apply(numgens I,i-> select(support unfolding_{i},m->not member(m,xs)));
    as1 := flatten as;
    if o.Verbose then <<netList apply(numgens I,i->apply(as_i, m->(degree m)_0)) << endl;
    rL := apply(#as,i->select(as_i,m->(degree m)_0> bound));
    if o.Verbose then <<netList apply(#rL,i->apply(rL_i,m->(degree m)_0))<<endl;
    restrictionList := apply(flatten rL,m->sub(m,A));
    (J,family) := getFlatFamily(I,A,unfolding,restrictionList);
    (J1,family1) := pruneFamily(I,J,family);
    cJ := decompose J1;
    --fixme: the following ignores the decomposition
    pt := findPoint(J1,2,10);
    if class pt === Nothing then return null;
    bs := gens ring J1;
    SA := ring family1;
    subPoint := apply(#bs,i->sub(bs_i,SA)=>sub(pt_(0,i),SA));
    family2 := sub(family1,subPoint);
    kk := coefficientRing SA;
    subPoint2 := apply(drop(support family2,#support I),m->m=>sub(random kk,SA));
    fib := ideal sub(sub(family2,subPoint2),ring I);
    fib)
--    if J1 == 0 then (
--	return fib := randomFiber(I,J1,family1)) else (<< betti J1<<endl;return numgens J1);
--  )

getFiber(List,List) := o -> (L,smallerList) ->(
    I:=ideal semigroupRing(L,BaseField=>ZZ/nextPrime 10^4);
    (A,unfolding):=makeUnfolding(I);
    xs:=(support unfolding)_{0..#L-1};
    as := apply(numgens I,i-> select(support unfolding_{i},m->not member(m,xs)));
    as1 := flatten as;
    restrictionList:=(apply(flatten as,m->sub(m,A)))_smallerList;
    (J,family) := getFlatFamily(I,A,unfolding,restrictionList);
    (J1,family1) := pruneFamily(I,J,family);
    cJ := decompose J1;
    --fixme: the following ignores the decomposition
    pt := findPoint(J1,2,10);
    if class pt === Nothing then return null;
    bs := gens ring J1;
    SA := ring family1;
    subPoint := apply(#bs,i->sub(bs_i,SA)=>sub(pt_(0,i),SA));
    family2 := sub(family1,subPoint);
    kk := coefficientRing SA;
    subPoint2 := apply(drop(support family2,#support I),m->m=>sub(random kk,SA));
    fib := ideal sub(sub(family2,subPoint2),ring I);
    fib)


-*
syzFormat=method()
syzFormat(List) := L -> (
    I := ideal semigroupRing(L,BaseField=>ZZ/nextPrime 10^4);
    fI := res I;
    apply(length fI+1,i->rank fI_i)
    )
*-
///--for thought
g=8
Lall=select(findSemigroups g,L->semigroupGenus L==g);#Lall
tally apply(Lall,L->syzFormat L)
Lknown=select(Lall,L->knownExample L);#Lknown
tally apply(Lknown,L->syzFormat L)
Lnotyetknown=select(Lall,L->not knownExample L);#Lnotyetknown
tally apply(Lnotyetknown,L->syzFormat L)
tally apply(Lnotyetknown,L->(#L,min L))
///


withRandomPoint=method(Options=>{Verbose=>false,"WithPoint"=>false,Probably=>false})

withRandomPoint(List,ZZ) := o -> (L,b) -> (
    I := ideal semigroupRing(L,BaseField=>ZZ/nextPrime 10^4);
    --fI=res I
    --fI.dd_3
    (A,unfolding) := makeUnfolding I;
-- b = g-3 -- this is a nice choice for b, but I have no way to say why in advance.
-- what is nice, is that the base is a cone over P1xP2
netList (as := apply(numgens I,i-> drop(support unfolding_{i},#L)));
if o.Verbose then <<netList apply(numgens I,i->apply(as_i, m->(degree m)_0)) << endl;
rL := apply(#as,i->select(as_i,m->(degree m)_0> b));
if o.Verbose then<<netList apply(#rL,i->apply(rL_i,m->(degree m)_0))<<endl;
restrictionList := apply(flatten rL,m->sub(m,A));
    (J,family) := getFlatFamily(I,A,unfolding,restrictionList);
    (J1,family1) := pruneFamily(I,J,family);
    cJ := decompose J1;
   if o.Verbose then << "number of components of the base = "<<#cJ<<endl;
   if o#"WithPoint" then if #cJ>1 then return apply(cJ,c->numgens c);
pt := findPoint(J1,2,10);
count:=2;
while(class pt === Nothing and count<20) do (count=count+1;
    pt=findPoint(J1,count,10));
if class pt == Nothing then return null;
bs := gens ring J1;
SA := ring family1;
subPoint := apply(#bs,i->sub(bs_i,SA)=>sub(pt_(0,i),SA));
family2 := sub(family1,subPoint);
kk := coefficientRing SA;
subPoint2 := apply(drop(support family2,#support I),m->m=>sub(random kk,SA));
fib := ideal sub(sub(family2,subPoint2),ring I);
dimSingularLocusOfFiber(fib,Probably=>o.Probably)
)

///
family = family1;J = J1
///
withRandomPoint(Ideal,Ideal,Matrix) := o -> (I,J,family) -> (
    --(J1,family1) := pruneFamily(I,J,family);
    cJ := decompose J;
    if o.Verbose then << "number of components of the base = "<<#cJ<<endl;
    if  o#"WithPoint" then if #cJ>1 then return apply(cJ,c->numgens c);
    S := ring I;
    dims:=apply(cJ,J2-> (
	    pt := findPoint(J2,2,10);
	    count:=2;
	    while(class pt === Nothing and count<20) do (count=count+1;
		pt=findPoint(J2,count,10));
	    if class pt === Nothing then return null;
	    assert(sub(J2, pt) == 0);
	    fiber:=ideal sub(family,vars S|pt);
	    assert(sub(J2, pt) == 0);
            assert(
	       checkFlatness(I,fiber)
	          );
     dimSingularLocusOfFiber(fiber,Probably=>o.Probably)
    ));
   min dims)
   
///
J_0
J1_0
-- 
///

withComponents=method(Options => {Verbose => false,Probably=>false})
withComponents(Ideal,List,Matrix) := o -> (I,cJ,family) -> (
    --if o.Verbose then <<" betti of components = " <<(for J in cJ list betti J)<< endl;
    answers := for J in cJ list (
	--(J1, family1) := pruneFamily(I,J,family);
--	wrp := withRandomPoint(I,J1,family1,Probably=>o.Probably);
	wrp := withRandomPoint(I,J,family,Probably=>o.Probably);
	if class wrp === Nothing then continue;
	wrp);
    if o.Verbose then <<"behavior of components =" <<answers <<endl;
    if answers == {} then return null else min answers
    )

///
restart
needsPackage "AIWeierstrass"
L = {5,6,7}
semigroupGenus L
I = semigroupIdeal( L, BaseField => ZZ/(nextPrime 10^4))
(A,unfolding) = makeUnfolding I;
elapsedTime (J, family) = getFlatFamily(I,A,unfolding);

L={6, 8, 10, 11, 13}
     I=ideal semigroupRing(L,BaseField=>ZZ/nextPrime 10^4);
     (A,unfolding)=makeUnfolding I;
     b = semigroupGenus L-3; 
     as=apply(numgens I,i->a=drop(support unfolding_{i},#L));
     rL=apply(#as,i->select(as_i,m->(degree m)_0> b));
     restrictionList=apply(flatten rL,m->sub(m,A));
     (J,family)=getFlatFamily(I,A,unfolding,restrictionList);
     (J2,family2)=pruneFamily(I,J,family);
     cJ=decompose J2
     assert(#cJ == 2)
     apply(cJ, J -> betti J)
     apply(cJ,J->withRandomPoint(I,J,family2))
     assert(withComponents(I,cJ, family2) == -1)
     withComponents(I,cJ, family2)
J1 = cJ_0
(J2, family3)= pruneFamily(I,J1,family2);
ring J2 === ring family2
#support J2
#support family2
///

ls = () -> run"ls -ltr"


familyWithSection=method(Options=>{Verbose=>false})
--Input: L, List of genertors of semigroups L
--Output: Boolean, true if the universal family has a syzygy forced section
--
familyWithSection(List) := o -> L -> (
    I:= semigroupIdeal L;
    fI:=res I;
    c:=#L-1;
    min (degrees fI_(c-1))_{#L..rank fI_(c-1)-1} > (degrees fI_c)_0)
    
testNW = method(Options=>{WithSectionOnly=>false})
testNW List := o -> L -> (
    if #L != 4 then error "expected a semigroup with 4 generators";
    if gcd L =!=1 then return (L,false);
    fL := res semigroupIdeal L;
    if rank fL_3 =!= 3 or rank fL_1 =!= 6 then
         return (L,false);
    m3 := matrix apply(flatten degrees fL_2,d->apply(flatten degrees fL_3,e->e-d));
    m2 := matrix apply(flatten degrees fL_1,d->apply(flatten degrees fL_2,e->e-d));
    if m3_(4,0)<0 and m2_(4,2) <min L then
         return (L, true) else
	 return (L, false))

testNWk = method(Options=>{WithSectionOnly=>false})
testNWk List := o -> L -> (
    if gcd L =!=1 then return (L,false);
    fL := res kunzIdeal L;
    if rank fL_3 =!= 3 or rank fL_1 =!= 6 then
         return (L,false);
    m3 := matrix apply(flatten degrees fL_2,d->apply(flatten degrees fL_3,e->e-d));
    m2 := matrix apply(flatten degrees fL_1,d->apply(flatten degrees fL_2,e->e-d));
    if m3_(4,0)<0 and m2_(4,2) <min L then
         return (L, true) else
	 return (L, false))
///
restart
needsPackage "AIWeierstrass"
L = {6,9,13,16}
testNW L
testNWk L
fL = res semigroupIdeal L
kL = res kunzIdeal L
betti fL
betti kL
///
testSubcomplex=method()

testSubcomplex(List) := L -> (
    if not gcd L ==1 then return false;
    if not #minimalSemigroupGens L==4 then return false;
    if syzFormat L !={1,6,8,3} then return false;
    fL:=res semigroupIdeal L;
    return (fL.dd_3_{0}^{4..7} == 0 and fL.dd_2^{4,5}_{0..3}==0))

testSubcomplex(ZZ,ZZ,ZZ,ZZ) :=(a,b,c,d) -> (
    L := {a,a+b,a+b+c,a+b+c+d};
    testSubcomplex L)

testSubcomplex(List,List,List,List) := (r1,r2,r3,r4) -> (
    LL := flatten flatten flatten for a in r1 list
    for b in r2 list
     for c in r3 list
      for d in r4 list(
	L := {a,a+b,a+b+c,a+b+c+d};
        (L,testSubcomplex(a,b,c,d))
	);
   apply(select(LL, L-> L_1 == true),L->L_0)
    )

///
r1=toList(6..9)
r2=toList(1..3)
r3=toList(1..3)
r4=toList(1..3)
5^2*10^2
elapsedTime LL=testSubcomplex(r1,r2,r3,r4);  -- 24.0722s elapsed
#LL
tally apply(LL,L->(
	I=semigroupIdeal L;
	fI=res I;
	J=ideal (fI.dd_1)_{0..3};
	fJ = res J;
	apply(4,i->rank fJ_i)=={1,4,4,1})
)
elapsedTime LLnW=apply(testNW(r1,r2,r3,r4),L->L_0);
#LLnW
tally apply(LL,L->#gaps L)
LLc=select(LL,L->not member(L,LLnW));
tally apply(LLc,L->#gaps L)
#LLc

netList apply(LLc,L->(fL=res semigroupIdeal L;(fL.dd_2)_{0..3}^{0..3}))
netList apply(LLc,L->(L,degreeMatrices L))
tally apply(LLc,L->(min L,((degreeMatrices L)_2)_(4,0)))
///


testNW(ZZ,ZZ,ZZ,ZZ) := o -> (a,b,c,d) ->(
    L := {a,a+b,a+b+c,a+b+c+d};
    testNW (L,o))

testNW(List, List, List, List) := o ->  (r1,r2,r3,r4) ->(
   LL := flatten flatten flatten for a in r1 list
    for b in r2 list
     for c in r3 list
      for d in r4 list(
	L := {a,a+b,a+b+c,a+b+c+d};
	testNW (L,o)
	);
   select(LL, L-> L_1 == true)
    )
testNW(List, List, List) := o -> (r1,r2,r3) ->(
   LL := flatten flatten flatten for a in r1 list
    for b in r2 list
     for c in r3 list
      (
	L := {a,a+b,a+b+c,a+b+c+b};
	testNW(L,o)
	);
   select(LL, L-> L_1 == true)
    )

testNWf=method(Options=>{WithSectionOnly=>false})
testNWf(List) := o -> L-> (
    if not gcd L ==1 then return (L,false);
    t:=symbol t;
    T:=ZZ[t];
    G:=gaps L;
    ap:=apery L;
    b:=sum(L)+ap#"conductor";
    HL:=sum(b,i->if not member(i,G) then t^i else 0);
    kos:=product(L,l->1-t^l);
    A:=(kos*HL)%t^b;
    --sa:= null;
    --A:=sum(subsets L, a->(sa=sum a; (-1)^(#a)*t^sa*(HL%t^(b-sa))));
    (M,C):=coefficients A;
    posMinus:=positions(flatten entries C,c->sub(c,ZZ)<0);
    posPlus:=positions(flatten entries C,c->sub(c,ZZ)>0);
    if not #posPlus==8+1 then return (L,false);
    if not #posMinus==3+6 then return (L,false);
    deg3:=reverse flatten last degrees M_posMinus_{0..2};
    deg2:=reverse flatten last degrees M_posPlus_{0..7};
    deg1:=reverse flatten last degrees M_posMinus_{3..8};
    --deg0:=reverse flatten last degrees M_posPlus_{8..8};
    --m3:=transpose matrix apply(deg3,d->apply(deg2,e->d-e));
    --m2:=transpose matrix apply(deg2,d->apply(deg1,e->d-e));
    if o.WithSectionOnly then  (L,deg3_0-deg2_4<0) else
    (L,deg3_0-deg2_4<0 and deg2_2-deg1_4<min L))

testNWf(List, List, List, List) := o ->  (r1,r2,r3,r4) ->(
   LL := flatten flatten flatten for a in r1 list
    for b in r2 list
     for c in r3 list
      for d in r4 list(
	L := {a,a+b,a+b+c,a+b+c+d};
	testNWf (L,o)
	);
   select(LL, L-> L_1 == true)
    )

testNWf(List, List, List) := o ->  (r1,r2,r3) ->(
   L:=null;
   LL := flatten flatten flatten for a in r1 list
    for b in r2 list
     for c in r3 list (
	L = {a,a+b,a+b+c,a+b+c+b};
	testNWf (L,o)
	);
   select(LL, L-> L_1 == true)
    )

///
restart
needsPackage"AIWeierstrass"
L = {7, 9, 38, 40}
testNWfWithAllDegreeConditions L
///
testNWfWithAllDegreeConditions=method(Options=>{AllDegreeConditions=>true})
testNWfWithAllDegreeConditions(List):= o -> L -> (
    if not gcd L ==1 then return (L,false);
    if not syzFormat L =={1,6,8,3} then return (L,false);
    t:=symbol t;
    T:=ZZ[t];
    G:=gaps L;
    ap:=apery L;
    b:=sum(L)+ap#"conductor";
    HL:=sum(b,i->if not member(i,G) then t^i else 0);
    kos:=product(L,l->1-t^l);
    A:=(kos*HL)%t^b;
    --sa:= null;
    --A:=sum(subsets L, a->(sa=sum a; (-1)^(#a)*t^sa*(HL%t^(b-sa))));
    (M,C):=coefficients A;
    posMinus:=positions(flatten entries C,c->sub(c,ZZ)<0);
    posPlus:=positions(flatten entries C,c->sub(c,ZZ)>0);
    if not #posPlus==8+1 or  not #posMinus==3+6 then (
--	<< "#posPlus and #posMinus  are "<<(#posPlus,#posMinus)<< flush <<endl;
    return (L,false));
    deg3:=reverse flatten last degrees M_posMinus_{0..2};
    deg2:=reverse flatten last degrees M_posPlus_{0..7};
    deg1:=reverse flatten last degrees M_posMinus_{3..8};
    m3:=transpose matrix apply(deg3,d->apply(deg2,e->d-e));
    m2:=transpose matrix apply(deg2,d->apply(deg1,e->d-e));
    if not o.AllDegreeConditions then return (L,deg3_0-deg2_4<0 and deg2_2-deg1_4<min L);
    if not ( deg3_0-deg2_4<0 and deg2_2-deg1_4<min L) then return (L,false);
    ijs:=flatten apply(4,i->apply(4,j->(i,j)));i:=null;j:=null;
    fourValues:=select(ijs,ij->(i=ij_0;j=ij_1; m2_(i,j)<0 or member(m2_(i,j),G)));
    twoVal1:=fourValues_{2,3}; --first 2x3 matrix
    row1:=twoVal1_0_0;
    pos1:=select(toList(0..3),j->not member(j,{twoVal1_0_1,twoVal1_1_1}));
    diff1:=m2_(row1,last pos1)-m2_(row1,first pos1);
    rowContainsLength2RegSequence1:=member(diff1,G);-- if they have a common factor
    -- then the difference has this factor as well;
    -- the assertion says that this is not the case;
    m3x2rows:=select(toList(0..3),i->not i==row1); 
    minorsCorrectDegree1:=(
    m2_(m3x2rows_1,twoVal1_0_1)+m2_(m3x2rows_2,twoVal1_1_1)==deg1_(m3x2rows_0) );
    answer1:=rowContainsLength2RegSequence1 and minorsCorrectDegree1 ;
    twoVal2:=fourValues_{0,1}; --second 2x3 matrix
    row2:=twoVal2_0_0;
    pos2:=select(toList(0..3),j->not member(j,{twoVal2_0_1,twoVal2_1_1}));
    diff2:=m2_(row2,last pos2)-m2_(row2,first pos2);
    rowContainsLength2RegSequences2:=member(diff2,G); -- if they have a common factor
    -- then the difference has this factor as well;
    -- the assertion says that this is not the case;
    m3x2rows2:=select(toList(0..3),i->not i==row2);
    minorsCorrectDegree2:=(
    m2_(m3x2rows2_1,twoVal2_0_1)+m2_(m3x2rows2_2,twoVal2_1_1)==deg1_(m3x2rows2_0) );
    answer2:=rowContainsLength2RegSequences2 and minorsCorrectDegree2 ;
    answer:=answer1 and answer2;
    if not answer then <<"degree conditions are  "<<answer <<flush<<endl;
    return(L,answer)
    )
///
elapsedTime tally apply(100,c->(
	count=0;
	while (
	    a=(6+random(100));
	    (b,c,d)=toSequence apply(3,i->1+random 100);
	    L={a,a+b,a+b+c,a+b+c+d};
	    not gcd L ==1 or not syzFormat L=={1,6,8,3}) do (count=count+1);
	<<"count =" <<count,<< ", L = "<<L <<flush <<endl;
	elapsedTime ((testNW L)_1,(testNWfwithAllDegreeConditions L)_1))
    )
-*
 -- 98.2159s elapsed

o15 = Tally{false => 91}
            true => 9
*-

count=0
elapsedTime tally apply(100,c->(
	while (
	    a=(6+random(100));
	    (b,c,d)=toSequence apply(3,i->1+random 100);
	    L={a,a+b,a+b+c,a+b+c+d};
	    not gcd L ==1 or not #minimalSemigroupGens L ==4 ) do (count=count+1);
	(syzFormat L)))

count
-*
o5 = Tally{false => 867}
           true => 133

o5 : Tally

i6 : 
o6 = 342
*-
count=0;
elapsedTime tally apply(1000,c->(
	while (
	    a=(6+random(100));
	    (b,c)=toSequence apply(2,i->1+random 100);
	    L={a,a+b,a+b+c,a+b+c+b};
	    not gcd L ==1 or not #minimalSemigroupGens L ==4 ) do (count=count+1);
	(syzFormat L=={1,6,8,3})))
count
 -- 232.976s elapsed
-*
o12 = Tally{false => 841}
            true => 159

o12 : Tally

i13 : 
o13 = 321
159/(1000+321)+0.0

*-
count=0
elapsedTime tally apply(100,c->(
	while (
	    a=(6+random(100));
	    (b,c,d)=toSequence apply(3,i->1+random 100);
	    L={a,a+b,a+b+c,a+b+c+d};
	    not gcd L ==1 or not #minimalSemigroupGens L ==4 ) do (count=count+1);
	(#socle L,syzFormat L)))

count

count=0
elapsedTime tally apply(100,c->(
	while (
	    a=(6+random(100));
	    (b,c,d)=toSequence apply(3,i->1+random 100);
	    L={a,a+b,a+b+c,a+b+c+d};
	    not gcd L ==1 or not #minimalSemigroupGens L ==4 or not #socle L==3) do (count=count+1);
	(syzFormat L)))

count

count=0
elapsedTime LLsoc3=apply(1000,c->(
	while (
	    a=(6+random(100));
	    (b,c,d)=toSequence apply(3,i->1+random 100);
	    L={a,a+b,a+b+c,a+b+c+d};
	    not gcd L ==1 or not #minimalSemigroupGens L ==4 or not #socle L==3) do (count=count+1);
	(L))); -- 388.15s elapsed
elapsedTime tally apply(LLsoc3,L->syzFormat L)  -- 74.6222s elapsed

LL1573=select(LLsoc3, L-> syzFormat L=={1,5,7,3});
elapsedTime LL1573wS=select(LL1573,L->(
	I=semigroupIdeal L;
	R=ring I;
	fI=res I;
        min (flatten degrees fI_2)_{4,5,6}>(degrees fI_3)_0_0)
);#LL1573wS
L=first LL1573wS
L=={60, 149, 165, 173}
#gaps L
I=semigroupIdeal L;R=ring I;
fI=res I
deg1 = flatten degrees fI_1
deg2 = flatten degrees fI_2
deg3 = flatten degrees fI_3
m3=matrix apply(deg2 ,d->apply(deg3,e->(e-d)))
m2=matrix apply(deg1 ,d->apply(deg2,e->(e-d)))
m1= matrix {deg1}
m1,m2,m3
apply(gens R,x->(x,degree x))
G=gaps L;
g=#G, Gi=G;
apply(3,i->(Gi=sums(Gi,G);(#Gi,(2*i+3)*(g-1))))
zeroes=matrix apply(5,i->apply(7,j->if not member(m2_(i,j),G) then m2_(i,j) else 0))
saturate minors(3,fI.dd_2_{0..3})



toString LL1463wS
LL1463wS={{66, 70, 71, 127}, {54, 115, 122, 163}}|{{79, 99, 122, 140}, {99, 129, 159, 244}, {34, 120, 179, 275}, {97, 195, 243, 262}, {94, 177, 238,
       240}, {68, 135, 179, 273}, {95, 176, 186, 274}, {69, 118, 162, 178}, {32, 70, 147, 189}, {15, 34,
       121, 197}, {86, 173, 267, 362}, {82, 171, 186, 206}, {88, 180, 194, 247}, {85, 182, 279, 287}, {87,
       184, 204, 250}}
#LL1463wS

LL1463=select(LLsoc3, L-> syzFormat L=={1,4,6,3});#LL1463
LL1463WithSection=select(LL1463,L->(
	I=semigroupIdeal L;
	R=ring I;
	fI=res I;
        min (flatten degrees fI_2)_{4,5}>(degrees fI_3)_0_0)
)

LL1463wS=sort(LL1463wS,L->#gaps L);
#LL1463wS
elapsedTime netList apply(LL1463wS,L->(
	I=semigroupIdeal L;
	R=ring I;
	fI=res I;
	sect=trim ideal fI.dd_3_{0};
	assert((gens I % sect) == 0);
	cMinors=decompose saturate minors(3,fI.dd_2_{0..3});
        (apply(gens R,x->(x,degree x)),#gaps L,cMinors, transpose fI.dd_3_{0}))
)

elapsedTime LL1793=select(LLsoc3, L-> syzFormat L=={1,7,9,3});
#LL1793
LL1793wS=select(LL1793,L-> (
	I=semigroupIdeal L;
	R=ring I;
	fI=res I;
        min (flatten degrees fI_2)_{4,5,6}>(degrees fI_3)_0_0));#LL1793wS

L=LL1463wS_0
L={15, 34, 121, 197}
I=semigroupIdeal L
#gaps L
S=ring I 
fI=res I
tex transpose fI.dd_1
tex fI.dd_2
tex fI.dd_3
degreeMatrices L
(decompose minors(3,(fI.dd_2)))_0==I
primaryDecomposition  minors(3,(fI.dd_2_{0..3}))
section=ideal fI.dd_3_{0}
gens I%(section)

--search 1463 formats with section
r1=toList(6..15);r2=toList(1..10);r3=toList(1..20);r4=toList(1..40);
23.4*2^3
elapsedTime LL1463a = flatten flatten flatten for a in r1 list
    for b in r2 list
     for c in r3 list
      for d in r4 list(
	L := {a,a+b,a+b+c,a+b+c+d};
	if not gcd L == 1 or not syzFormat L=={1,4,6,3} then continue;
	I=semigroupIdeal L;
	if (degreeMatrices L)_2_(4,0) >= 0 then continue;
	(L,(degreeMatrices L)_2_(4,0))
	);
#LL1463a
first LL1463a, last LL1463a
LL1463as=sort(LL1463a,Ld->#gaps Ld_0)
LL1463s=apply(LL1463as,Ld->(#gaps Ld_0,Ld_1,Ld_0))	
#LL1463s
-- for the tex file
L=LL1463s_2
I=semigroupIdeal L_2
S=ring I
fI=res I
tex (radical minors(3,fI.dd_2_{0..3}))_0
fI.dd_3
tex transpose fI.dd_1
tex fI.dd_2
tex transpose fI.dd_3
---
m3=matrix apply(deg2 ,d->apply(deg3,e->(e-d)))
m2=matrix apply(deg1 ,d->apply(deg2,e->(e-d)))
m1= matrix {deg1}
m1,m2,m3
L
G=gaps L;
g=#G, Gi=G;
apply(3,i->(Gi=sums(Gi,G);(#Gi,(2*i+3)*(g-1))))
///


///

A=toList(6..45)
B=toList(1..15)
C=toList(1..30)
D=toList(1..15)
N=#A*#B*#C*#D
N/1250*16.19/60
elapsedTime LLf=testNWf(A,B,C,D); -- 11347.7s elapsed
elapsedTime LLh=addDataToListOfLnW(LLf,10); -- 1163.52s elapsed

openOut "LLh45-15-30-15s"
"LLh45-15-30-15s" << toString LLh
"LLh45-15-30-15s" <<close
ls()
///

///
last LLha
L=(last LLf)_0
I=semigroupIdeal L
R=ring I
J=ideal (gens I)_{0..3}
fJ=res J
I0=ideal(gens I%R_0)
fI0=res I0

fI0.dd_2,fI0.dd_3
fI=res I
fI.dd_2,fI.dd_3
sm2x4=syz (m2x4=fI.dd_2^{4,5}_{4..7})
sm2x4%fI.dd_3^{4..7}_{1,2}
#LLf/N+0.0
elapsedTime LL=testNW(A,B,C,D); -- 6787.09s elapsed-- 879.122s elapsed
#LL/N+0.0
#LL
elapsedTime LLh=addDataToListOfLnW(LL,10);  -- 1145.15s elapsed -- 96.3114s elapsed
(6787.09+1145.15)/60

elapsedTime LLh=sort(LLh,Lh->Lh_1);
T=tally (gs=apply(LLh,Lh->Lh_1))
tally values T
missinggs=select(toList(min gs..max gs),g->not member(g,gs))
first LLh
tally apply(LLh,Lh-> Lh_2)
tally apply(LLh,Lh->(Lh_3_0-Lh_3_2))
tally apply(LLh,Lh->Lh_{4,7})
LLh12=select(LLh,Lh->Lh_7==12);
LL12m=apply(LLh12,Lh->degreeMatricesOLd Lh_0);
first LL12m
netList apply(LLh12,Lh->(L=Lh_0;fI=res semigroupIdeal L;degM=degreeMatricesOld L;(L,L_1,fI.dd_3_{0},degM_1,fI.dd_2_{0..3})))
openOut "LLh45-15-30-15"
"LLh45-15-30-15s" << LLh
"LLh45-15-30-15" <<close
ls()
#LLh

///

///
restart
needsPackage "AIWeierstrass"
LLh=value get "LLh45-15-30-15s";
#LLh
elapsedTime tally apply(LLh,Lh->(
	L=Lh_0;
	I=semigroupIdeal L;
	M=syz (gens I)_{0..3};
	assert(rank source M==4);
	#select(flatten entries M,m->m==0)))   -- 102.51s elapsed
--o4 = Tally{4 => 3460}

elapsedTime tally apply(LLh,Lh->(
	L=Lh_0;
	I=semigroupIdeal L;
	M=syz (gens I)_{0..3};
	radical minors(3,M)== ideal (gens I)_{0..3})) -- 419.792s elapsed
--o5 = Tally{true => 3460}

elapsedTime tally apply(LLh,Lh->(
	L=Lh_0;
	I=semigroupIdeal L;
	M=syz (gens I)_{0..3};
	saturate minors(3,M)== ideal (gens I)_{0..3}))  -- 167.805s elapsed
--o6 = Tally{true => 3460}

netList apply(LLh_{0..9},Lh->(L=Lh_0;I=semigroupIdeal L;
	M=syz (gens I)_{0..3};G=gaps L;
	T=tally flatten apply(4,i->apply(4,j->Lh_10_(i,j)>0 and not member(Lh_10_(i,j),G)));
	(Lh_{10},M,T)))

elapsedTime tally apply(LLh,Lh->(L=Lh_0;I=semigroupIdeal L;
	M=syz (gens I)_{0..3};G=gaps L;
	T=tally flatten apply(4,i->apply(4,j->Lh_10_(i,j)>0 and not member(Lh_10_(i,j),G)));
	T))  -- 114.167s elapsed

--o8 = Tally{Tally{false => 4} => 3460}
--                  true => 12


elapsedTime tally (fourVals= apply(LLh,Lh->(L=Lh_0;I=semigroupIdeal L;
	M=syz (gens I)_{0..3};G=gaps L;
	ijs=flatten apply(4,i->apply(4,j->(i,j)));
	fourvalues=select(ijs,ij->(i=ij_0;j=ij_1; Lh_10_(i,j)<0 or member(Lh_10_(i,j),G)));
	fourvalues))) -- 124.701s elapsed

--o9 = Tally{{(0, 2), (0, 3), (3, 0), (3, 1)} => 1149}
--           {(1, 1), (1, 3), (3, 0), (3, 2)} => 1641
--           {(1, 2), (1, 3), (3, 0), (3, 1)} => 292
--           {(2, 0), (2, 3), (3, 1), (3, 2)} => 151
--           {(2, 1), (2, 2), (3, 0), (3, 3)} => 128
--           {(2, 1), (2, 3), (3, 0), (3, 2)} => 99


elapsedTime tally (twoRegSequences= apply(LLh,Lh->(
	L=Lh_0;
	G=gaps L;
	ijs=flatten apply(4,i->apply(4,j->(i,j)));
	fourValues=select(ijs,ij->(i=ij_0;j=ij_1; Lh_10_(i,j)<0 or member(Lh_10_(i,j),G)));
	twoVal1=fourValues_{0,1};
	row1=twoVal1_0_0;
	pos1=select(toList(0..3),j->not member(j,{twoVal1_0_1,twoVal1_1_1}));
	diff1=Lh_10_(row1,last pos1)-Lh_10_(row1,first pos1);
	twoVal2=fourValues_{2,3};
	row2=twoVal2_0_0;
	pos2=select(toList(0..3),j->not member(j,{twoVal2_0_1,twoVal2_1_1}));
	diff2=Lh_10_(row2,last pos2)-Lh_10_(row2,first pos2);
	member (diff2,G) and member(diff1,G)
	)))  -- 25.6386s elapsed
--o10 = Tally{true => 3460}	    


    
T=tally apply(LLh,Lh->Lh_1)
genusGaps=select(toList(min keys T..max keys T),g ->not member(g,keys T))
tally values T

first LLh
tally apply(LLh,Lh->(Lh_7,Lh_3_0-Lh_3_2))
LLh9=select(LLh,Lh->Lh_7==9);#LLh9
netList apply(LLh9,Lh->(Lh_{0,1,2,3}))
apply(LLh9,Lh->(L=Lh_0;I=semigroupIdeal L;fI=res I;fI.dd_3_{0}))
tally apply(LLh,Lh->Lh_7)
tally apply(LLh,Lh->Lh_2)
T=tally apply(LLh,Lh->Lh_1)
max values T
pos=positions(values T,v->v==26)
(keys T)_pos
LLh73=select(LLh,Lh->Lh_1==(keys T)_pos_0);
netList apply(LLh73,Lh->Lh_{0,1,2,7})
tally apply(LLh73,Lh->Lh_{2,7})
tally apply(LLh,Lh->Lh_2)
tally apply(LLh,Lh->Lh_3_1)
tally apply(LLh,Lh->(Lh_7,Lh_3_0-Lh_3_2))
LLh1=select(LLh,Lh->Lh_7==1);
tally apply(LLh,Lh->(Lh_3_0-Lh_3_2))
LLh1a=select(LLh1,Lh->(Lh_3_0-Lh_3_2)==0);
#LLh1a,#LLh1,#LLh
LLh1b=select(LLh,Lh->(Lh_3_0-Lh_3_2)==0);
LLh1b==LLh1a
T1g=tally apply(LLh1a,Lh->Lh_1);
tally values T1g
min keys T1g,max keys T1g
gs1Gaps=select(toList(min keys T1g..max keys T1g),g->not member(g,keys T1g))
tally apply(gs1Gaps,g->g%6)
LLh119=select(LLh,Lh->Lh_1==119);
tally apply(LLh119,Lh->Lh_{2,3,7,1,0})
///

testNWListOfLists = method()
testNWListOfLists List := LL -> (
    LL1 := select(LL, L-> (testNW(L, WithSectionOnly => true))_1);
    if LL1 == {} then return {};
    LL2 := select(LL1, L -> numericalProofOfNonWeierstrass L);
    apply(LL2, L->(L,true))
    )

numericalProofOfNonWeierstrass=method()
numericalProofOfNonWeierstrass(List) := L -> (
    fL := res semigroupIdeal L;
    m3 := matrix apply(flatten degrees fL_2,d->apply(flatten degrees fL_3,e->e-d));
    m2 := matrix apply(flatten degrees fL_1,d->apply(flatten degrees fL_2,e->e-d));
    m3_(4,0)<0 and m2_(4,2) <min L)

makeArithmeticProgression = (N,start,dif) ->(
   --arithmetic progression of 4-gen semigroups
   apply(N, n-> (
	   a := start+n;
	   {a,a+dif, a+2*dif, a+3*dif}
	   )))

addData=method()
addData(List,ZZ) := (L,n) -> (
    if not class L === List then error "expected a semigroup";
    g:=semigroupGenus L; G := gaps L; ewtL:=ewt L;    
    wtL:=weight L; m:=min L;
    diffs:=(L_1-L_0,L_2-L_1,L_3-L_2);
    Gi:=G;buchDiffs:=apply(4,i->(Gi=sums(Gi,G);(2*i+3)*(g-1)-#Gi));
    if n<=6 then return toSequence (L,g,m,diffs,buchDiffs,wtL,ewtL)_{0..n};
    fI:= res semigroupIdeal L;
    M:=(degreeMatricesOld L)_1;
    degs:=(flatten degrees fI_1,(degree fI_3_0)_0,(degree fI_2_4)_0);
    kk:=coefficientRing ring fI;
    A4:=kk[support (fI.dd_1)];
    degSection:=degree ideal sub(fI.dd_3_{0},A4);    
    n0 := min(n,10);
    return toSequence (L,g,m,diffs,buchDiffs,wtL,ewtL,degSection,degs,G,M)_{0..n0}
)

addDataToListOfLnW=method()

addDataToListOfLnW(List,ZZ) := (LL,n) -> if class (first LL) === Sequence then (
        apply(LL,L->addData(L_0,n))) else ( apply(LL,L->addData(L,n)))
///
restart
needsPackage "AIWeierstrass"
L = {6,9,13,16}
testNW L






























































aL = apery L
bb = L -> (
    aL := apery L;
    m := aL#"multiplicity";
    bb := for i from 1 to m-1 list
             for j from i to m-1 list(
	       c := (aL#i+aL#j -
		   if i+j != m then
		       aL#((i+j)%m) else 0)//m;
	       {(i,j),(if i+j!= m then c else c+1)});
    hashTable flatten bb)

cc = (L,i,j) -> (
    B := bb L;
    m := min L;
    if i+j=!=m then B#(i,j) else B#(i,j)-1)

elapsedTime LL = for i from 1 to 1000 list(
	L = apply(4, j-> random 100);
	if (gcd L =!= 1 or
#minimalSemigroupGens L =!= 4) then continue;
L);
elapsedTime apply(LL, L ->(
--	R := semigroupRing L;
--        R = kunzRing L;
--        H = HH koszul vars R ;
  --      for i from 1 to 3 list
--	  degrees target gens H_i
testNW L
--F := res monomialIdeal ideal R;
--for i from 1 to 3 list degrees F_i
));


-- 14.0899s elapsed	
L = {6,9,13,16}
R = semigroupRing L    
K = koszul vars R

H = HH K;
netList for i from 0 to 3 list degrees target gens H_i

///


LabBookProtocol = method(Options=>{Verbose=>true,BaseField=>ZZ/nextPrime 10^4,ProbTest=>true})

LabBookProtocol List := o -> L -> (
    LLnWdone:={{6, 9, 13, 16}, {8, 10, 13, 15}, {8, 9, 12, 13}};--, {6, 9, 14, 17} };
    
    if o.Verbose then <<"genus of L = "<<L<<" is "<<semigroupGenus L<<flush<<endl;
    if not #L==4 or not syzFormat L == {1,6,8,3} then (
           error  ("expected a semigroup with 4 generators and syzformat {1,6,8,3}"));
    I := semigroupIdeal L;
    fI := res I;
    if not min (degrees (fI_2)_{4..7})_1 > (degrees fI_3_{0})_1_0 then  (
	<< "The universal family of the semigroup ",L,
	<<" has no obvious section."<<flush<<endl;
	return null);
    kk := coefficientRing ring I;
    A4ungraded:= kk[support I];
    if o.Verbose then (
	<<"The degree of the multivalued section is = "<<degree sub(ideal fI.dd_3_{0},A4ungraded)<<"."<<flush<<endl
		   );
    if not member(L,LLnWdone) then ( <<"A computational proof, that the semigroup L = "<< L <<
	" is not Weierstrasse," <<flush<<endl;
	<<"is not yet documented.  " <<flush<<endl; return null);

    if L=={6, 9, 13, 16} then (
	<< "expected elapsedTime is = 1821.35 seconds" <<flush<<endl;
	
	print "
        
        --probabilistic argument:
	elapsedTime verifyNotWeierstrass({6, 9, 13, 16},Verbose=>true,BaseField=>ZZ/nextPrime 10^4,ProbTest=>true);
	-- computational proof for char 0; 
	elapsedTime verifyNotWeierstrass({6, 9, 13, 16},ProbTest=>false,BaseField=>ZZ/nextPrime 10^6,Factor=>2^5,Bound=>1100)
	
	");
    if L=={8, 10, 13, 15} then (
	<< "expected elapsedTime is = 157.955 seconds" <<flush<<endl;

	print "

        --probabilistic argument:
        elapsedTime verifyNotWeierstrass({8, 10, 13, 15},Verbose=>true,BaseField=>ZZ/nextPrime 10^4,ProbTest=>true)
   
        -- computational proof in char 0;  
        elapsedTime verifyNotWeierstrass({8, 10, 13, 15},ProbTest=>false)
              --,Verbose=>true,BaseField=>ZZ/nextPrime 10^4,ProbTest=>false;Factor=>1)
	
	");
	      
    if L=={8,9,12,13} then (
	<< "expected elapsedTime is = 486.049 seconds" <<flush<<endl;
        print "

        --probabilistic argument:
	elapsedTime verifyNotWeierstrass({8, 9, 12, 13},Verbose=>true,BaseField=>ZZ/nextPrime 10^4,ProbTest=>true)
   
        -- computational proof in char 0;  
        elapsedTime verifyNotWeierstrass({8, 9, 12, 13},ProbTest=>false)

	"
        );
     )

 verifyNotWeierstrass=method(Options=>{Verbose=>true,
	BaseField=>ZZ/nextPrime 10^4,ProbTest=>true,Factor=>1,Bound=>200})
--Input: L a semigroup with 4 generators
--       of format {1,6,8,3}
--Output: Boolean
verifyNotWeierstrass(List):= o -> L -> (
    assert(#L==4 and syzFormat L =={1,6,8,3});
    I:=semigroupIdeal(L,BaseField=>o#BaseField);
    betti(fI:=res I);
    (A,unfolding):=makeUnfolding I;
    degsA:=unique flatten degrees A;
    posList:=prepareInitialPositionList;(L,toList(min degsA.. max degsA));
    (J,family) := if o.Verbose then (elapsedTime getFlatFamily(I,A,unfolding)) else (
	getFlatFamily(I,A,unfolding));-- 919.902s elapsed
    (J1,family1):=if o.Verbose then (elapsedTime pruneFamily(I,J,family)) else (
	pruneFamily(I,J,family));
    if o.Verbose then <<"betti J1 = "<<betti J1<<flush<< endl;
    kk:=coefficientRing A;
    A4 := kk[support I,Degrees=>apply(support I,m->degree m)];
    gJ1 := gens ring J1;
    if o.Verbose then <<"probabilistic Test :"<<flush <<endl;
    drs:=apply(2, n->(
	    point := findPoint J1;
	    subList1:=apply(#gJ1, i-> ((gJ1)_i => point_(0,i)));
	    subList2:=apply(#gJ1, i->
		(sub((gJ1)_i,ring family1) => sub(point_(0,i), kk)));
	    subList3 :=apply (#L, i->((ring family1)_i => A4_i));
	    fiber := sub(family1, subList3|subList2);
	    assert(sub(J1, subList2) ==0);
	    sing :=ideal singularLocus ideal fiber;
	    (dim (sing),radical sing,fiber))
	);
     if o.Verbose then (
        <<"tally of the dimension singularities of 2 fiber = "<<tally apply(drs ,dr->dr_0)<<flush<<endl;
        << "singular points = " << netList apply(drs,dr->dr_1) <<endl;);
     if o.ProbTest then (
	 fiber:=drs_0_2;
	 A4=ring fiber;
	 t:=symbol t;
	 P4:=kk[gens A4|{t},Degrees=>degrees A4|{1}]; --a weighted P4
	 fibt:=ideal homogenize(sub(fiber,P4),t);
	 F:=res  fibt;
	 sect:=trim ideal F.dd_3_{0};
	 assert(sect== homogenize(sub(drs_0_1,P4),t));
	 gJ:=ideal((gens fibt)_{0,1,2,3});
	 FgJ:=res gJ;
	 assert(rank FgJ_3==1);
	 assert(ideal(FgJ.dd_3)==sect);
	 pos:=select(3,i->(FgJ.dd_2)_(3,i)==0);
	 assert(#pos==2);
	 m3x2:=FgJ.dd_2_pos^{0..2};
	 assert(m3x2%sect==0);
	 assert(minors(2,m3x2)==ideal(gens fibt)_{0..2});
	 three:=ideal (gens homogenize(sub(drs_0_1,P4),t))_{1..3};
	 if o.Verbose then( << "entries of the 2x3 matrix modulo three section equations"<<flush<<endl;
	     <<"factored are "<< flatten entries (m3x2%three)/factor<<flush<<endl;);
	 return (gens fibt)_{0..3}%(sect^2) == 0 and m3x2%sect==0);
     -- Lift to characteristic zero
     if not J1==0 then (<<"need a different method to lift" <<endl;return null);
     if not o.ProbTest then (
	  n:=o.Factor;b:=o.Bound;
	  fF:=res ideal family1;
	  assert(betti fF==betti res I);
	  (M,C):=coefficients (n*fF.dd_1);
	 TC:=tally flatten entries sub(C,kk);
	 ma:=max apply(keys TC,k->abs sub(k,ZZ));
	 if o.Verbose then (<< "coefficients bounded by "
	            <<ma<<flush<<endl;);
	 assert(ma<b);	
	 (M2,C2):=coefficients (n*fF.dd_2);
	 TC2:=tally flatten entries sub(C2,kk);
	 assert(max apply(keys TC2,k->abs sub(k,ZZ))<b);
	 S:=ZZ[support family1,Degrees=>apply(support family1,m -> degree m)];
	 betti(fF1ZZ:=sub(n*fF.dd_1,S));
         betti(fF2ZZ:=sub(n*fF.dd_2,S));
	 if o.Verbose then elapsedTime prod:=(fF1ZZ*fF2ZZ) else (
	     prod=(fF1ZZ*fF2ZZ)
	 );
         assert(prod==0);
	 if o.Verbose and prod==0 then <<"The family is flat over an open part of Spec ZZ!"<<flush<<endl;
	 (M3,C3):=coefficients (n*fF.dd_3);
	 TC3:=tally flatten entries C3;
	 assert(max apply(keys TC3,k->abs sub(k,ZZ))<b);
	 betti(fF3ZZ:=sub(n*fF.dd_3,S));
	 assert(fF2ZZ*fF3ZZ==0);
	 betti (section:=ideal fF3ZZ_{0}^{0..3});
	 --assert(ideal FgJZZ.dd_3==section); -- => gJ is the syzygy scheme fF3.dd_{0}
	 --if o.Verbose then (<< "syzygy matrix of J mod the section is zero is " <<
	 --    FgJZZ.dd_2%section==0 <<" !"<<flush<<endl;);
	 if
	    rank source gens trim ideal (n^2*fF1ZZ%(section^2))<3
	  then
	 (<< "The semigroup L = " <<L<<" is not Weierstrass!"
	     <<flush<<endl;);
	 true)
        )
kunzRing = method(
    Options => {"BaseField" => ZZ/(nextPrime 10^4),
	"VariableName" => getSymbol "x"})

kunzRing List := Ring => L -> (
    --returns the semigroup ring of R mod the multiplicity element
    R := semigroupRing(L);
    m := min(gens R/degree);
    newvars := select(gens R, x -> degree x > m);
    newdegs := select(gens R/degree, d -> d>m);
    S := coefficientRing R[newvars, Degrees => newdegs];
    S/sub(ideal R, S)
    )


-- kunzIdeal = method(Options => {
-- 	"BaseField" => ZZ/(nextPrime 10^4),
-- 	"VariableName" => getSymbol "x"})
kunzIdeal = method()
kunzIdeal List := Ring => L -> (
    --returns the semigroup ring of R mod the multiplicity element
    m := min L;
    L' := drop(L,1);
    I := semigroupIdeal L;
    kk := coefficientRing ring I;
    S' := kk[(gens ring I)_{1..numgens ring I -1}, Degrees => L'];
    sub(ideal I, S')
    )

    ///
restart
needsPackage "AIWeierstrass"
L = {6,9,13,16}
I = semigroupIdeal L
Ik = kunzIdeal L
betti res I ==betti res Ik

LL = for i from 1 to 100 list(
    L := apply(4, j-> random(100));
    if gcd L !=1 or
    (L = minimalSemigroupGens L;
        #L != 4)
    then continue;
    L);
#LL -- 45
elapsedTime for L in LL do
    res semigroupIdeal L
elapsedTime for L in LL do
    res kunzIdeal L
elapsedTime for L in LL do
    minimalBetti kunzIdeal L
elapsedTime for L in LL do
    testNW L --.91
elapsedTime for L in LL do
    testNWk L --.97
elapsedTime for L in LL do
    testNWf L --1.7
///


kunzWaldi = method()
kunzWaldi(ZZ,ZZ) := (p,q) -> (
    if gcd(p,q) !=1 then error "p,q should be relatively prime";
    X := toList (1..q//2);
    Y := toList(1..p//2);
    Z := X**Y;
    sgrps := flatten (for i from 0 to #Z-2 list
	              for j from i+1 to #Z-1 list
	sort{p,q,
	    p*q - Z_i_0 * p - Z_i_1 * q,
	    p*q - Z_j_0 * p - Z_j_1 * q}
	);
    select(sgrps, s -> #minimalSemigroupGens s == 4)
	)
///
restart
needsPackage "AIWeierstrass"
p = 6;q=13
kw = kunzWaldi(7,9);#kw
p = 6
kwGood  = for q from 10 to 20 list (
    if gcd(p,q) !=1 then continue;
good = select(kunzWaldi(p,q),s ->(
	testNWfWithAllDegreeConditions s)_1);
if good == {} then continue else good
)
(flatten kwGood)_0
netList apply(flatten kwGood, L -> ((semigroupGenus L), L))

kw  = kunzWaldi(6,17)
select(kunzWaldi(14,17), L -> L == {6,9,14,17})
testNWfWithAllDegreeConditions (L = {6,9,14,17})
semigroupGenus L

I = semigroupIdeal{6,9,13,16}
betti res (ideal I_*_{0,1,2})
betti res (ideal I_*_{1,2,3})
betti res (ideal I_*_{1,4,5})

I = semigroupIdeal{6,9,14,17}
length res (ideal I_*_{0,1,2})
length res (ideal I_*_{1,2,3})
length res (ideal I_*_{1,4,5})

for c from 4 to 10 list(
    if c%3 == 0 then continue;
    I := semigroupIdeal{6,9,c+9,c+12};
    ell :=
    {length res (ideal I_*_{0,1,2}),
    length res (ideal I_*_{1,2,3}),
    length res (ideal I_*_{1,4,5})}
    all apply(ell, i -> ell_i == 3)
    )


///
pseudoFrobenius = method()
pseudoFrobenius List := L -> (
--computes the pseudoFrobenius numbers of the
--semigroup generated by L (these are the gaps h
--such that s+h is in the semigroup for all s in the
--semigroup; The canonical module is generated by
--{t^(-h) | h is a pseudoFrobenius number.
    s := sum L;
    fL := res semigroupIdeal L;
    D := flatten degrees (fL_(length L-1));
    apply(D, d-> d-s)
    )

syzFormat = method()
syzFormat Complex := F -> apply(1+length F, i -> rank F_i)
syzFormat Ideal := I -> syzFormat res I
syzFormat List := L -> syzFormat semigroupIdeal L

degreeMatrices = method()
degreeMatrices Complex := F-> (
    c:=length F;
    ms:=apply(c,i-> matrix apply(flatten degrees F_i,d->
	                   apply(flatten degrees F_(i+1),e->e-d)));
    ms)
degreeMatrices Ideal := I -> degreeMatrices res I
degreeMatrices List := L-> degreeMatrices semigroupIdeal L

-* Documentation section *-
beginDocumentation()

doc ///
Key
  AIWeierstrass
Headline
  Harnessing ML to find Weierstrass semigroups
Description
  Text
    We implement an algorithm based on Henry Pinkham's thesis
    that can check whether a given numerical semigroup
    is the Weierstrass semigroup of pole orders at a
    point on a compact Riemann surface.


    Though in principle it would be possible with this
    algorithm to show that a given semigroup does not
    occur as a Weierstrass semigroup, this seems out
    of reach of current computation. However the algorithm
    can often show that a semigroup DOES occur as a
    Weierstrass semigroup.

    The algorithm starts with a numerical semigroup L of
    semigroupGenus g (that is, with g gaps) and forms the semigroup
    ring k[L] = S/I, over a field k (typically of
    finite characteristic, to improve computational
    efficiency), where S is a polynomial ring and
    I = (f_1,\dots, f_r). This is a homogeneous ideal with respect
    to the grading by the degrees in the semigroup.

    We then form an unfolding of I;
    that is we add to each generator f_i a sum of terms u_i*m_i
    with the  m_i monomials of degree < the degree of f_i and the u_i
    new variable of degree deg u_i= deg f_i-deg m_i. Thus we 
    obtaining homogeneous polynomial F_i in the polynomial ring S[U]
    where U is the union of all u_i's. (The
    universal unfolding would be the case where we
    add all  monomials).

    We next compute the flattening relations: that is
    the equations J \subset k[U] such that
    he S[U]/(F_1,\dots F_r, J) is flat over k[U]/J.

    Finally we pick a random point of Spec k[U]/J,
    with corresponding maximal ideal m,
    and test whether the fiber S[U]/(m+(F_1,\dots F_r))
    is nonsingular. If it is, then L is a Weierstrass
    semigroup.

    (By Pinkham's theorem, if we could pick a ``general point'', then this test would be
    necessary as well as sufficient.)

    To prove that L is Weierstrass it suffices to produce a smooth fiber correponding to
    the flat family which uses only a subset of the variables U.

    Our AI hope is that a machine could get a good guess about the nature of these smaller families,
    so that we can verify that a semigroup is Weierstrass in a larger range of examples.

    These computation over a finite field, can be lifted to the integers in case the coefficients
    in the equations of the flattening relations are small, proving that the semigroup is Weierstrass
    over the field of complex numbers CC.

    In the following, L is the list of generators of a semigroup that is Weierstrass.
    The function @TO testWeierstrass@(L,n) returns the dimension of the singular locus
    of a random fiber of a family using only unfolding variables of degree >n. The
    output 0 thus means that this fiber is singular, while the output -1
    means that it is smooth.
  
  Example
    L = {4,5,6,7}
    semigroupGenus L
    testWeierstrass(L, 13)
    testWeierstrass(L, 6)
References
     \textit{Pinkham, Henry C.},
       Deformations of algebraic varieties with \(G_m\) action,
       Ast{\'e}risque t\extbf{20} (1974), pp 1 - 131,
       Soci{\'e}t{\'e} Math{\'e}matique de France (SMF), Paris
SeeAlso
   testWeierstrass
Subnodes
   combinatorialFunctions
   commutativeAlgebra
   dataFunctions
   forSergeiAndGiorgi
///

document {
Key => combinatorialFunctions,
Headline => "Combinatorial functions concerning numerical semigroups",
   "A numerical semigroup is a subset L of the nonegative integer closed under addition,
    whose complement, the set of gaps G=mathbb N setminus L, is finite.
    Example of such semigroups L=L(X,p) for X a smooth projective curve and p in X a point, 
    are given by the order of poles at p of rational (or meromorphic) functions on X which
    which are regular on X setminus p.
    The number of gaps coincides with the genus of the algebraic curve (by Riemmann-Roch).
    Such semigroups are called Weierstrass semigroups.",
    PARA{},
    "We call the number of gaps the semigroupGenus of L for any semigroup L.
     Not every semigroup is Weierstrass, the first example where discovered by Buchweitz.",

     PARA{},
     SUBSECTION "Numerical invariants of semigroups",
     UL{
        TO gaps,
	TO semigroupGenus,
	TO isGapSequence,
	TO aperySet,
	TO apery,
	TO weight,
	TO ewt,
	TO socle,
	TO type,
	TO sums,
	TO minimalSemigroupGens,
        },
    
     SUBSECTION "Buchweitz criterion",
     UL{
	TO buchweitz,
        TO buchweitzCriterion,
	TO buchweitzSemigroups,
        },
    
     SUBSECTION "Listing",
     UL{
	TO findSemigroups,
	TO knownExample,
        }        
}

document {
Key => commutativeAlgebra,
Headline => "commutative Algebra functions",
    "The semigroup ring of the semigroup L over a field K is the k-algebra

     K[L] = < t^l, l in L> subset K[t].
  
    These a class of algebras widely studied by Herzog, Kunz and many others.",

     PARA{},
     SUBSECTION "Basic functions",
     UL{
        TO semigroupRing,
	TO semigroupIdeal,
        },
    
     SUBSECTION "Deformations",
     UL{
	TO def1,
        TO makeUnfolding,
	TO flatteningRelations,
	TO restrictedUnfolding,
	TO getFlatFamily,
	TO pruneFamily,
	TO showRestrictedFamily,
	TO findPoint,
	TO getFiber,
	TO checkFlatness,
	TO dimSingularLocusOfFiber,
	TO liftToCharacteristicZero,
	TO minimalPositionLists,
        },
    
     SUBSECTION "Testing Weierstrass",
     UL{
	TO withRandomPoint,
	TO withAffineBase,
	TO withComponents,
	TO testWeierstrass,
	TO testWeierstrassRange,
	TO familyWithSection,
	TO testNW,
	TO numericalProofOfNonWeierstrass,
	TO verifyNotWeierstrass,
	TO testNWfWithAllDegreeConditions,
        },
    SUBSECTION "Improving the families",
     UL{
	TO optimalBound,
	TO optimalRange,
	TO shrinkRange,
	TO prepareInitialPositionList,
	TO systematicShrinking,
	TO reverseSorting,	
	TO showRestrictedFamily,
	TO liftToCharacteristicZero,
        },
    SUBSECTION "Collecting data",
     UL{
	TO produceData,
	TO produceBounds,
	TO produceRangesFromBounds,
	TO produceShrinkedRangesFromRanges,
	TO produceMinListsFromRanges,
	TO produceMinimalFamiliesFromMinLists,
	TO continueComputation,
	TO displayMinimalFamilies,
	TO addData
        }, 
}

document {
Key => dataFunctions,
Headline => "data",
    " In section we collect a few functions which extract discrete informations",
     PARA{},
     SUBSECTION "Arrays",
     UL{
        TO positionListToArray,
	TO positionArrayToList,
	TO degreeArray,
	TO dataForML,
	TO syzFormat,
        },
    
     SUBSECTION "Collecting training data",
     UL{	
        TO findSemigroups,
	TO produceData,
	TO produceBounds,
	TO produceRangesFromBounds,
	TO produceMinListsFromRanges,
	TO continueComputation,
	TO displayMinimalFamilies,
	TO testNW,
	TO addData,	
	}
}

document {
Key => forSergeiAndGiorgi,
Headline => "Explanation of the data available",

     "Starting with a singular curve C_0  defined by a semigroup L
     in an affine space AA^n, where n is the number of generators of L, we 
     define an ideal by adding
     terms to each equation of C_0, yielding the  so-called universal unfolding.
     The added terms in the i-th equation of C_0 have the
     form a_{i,j}*m_{i,j}, where m_{i,j} is one of the monomials of
     degree < the degree of the i-th equation and is not
     in the ideal of leading terms of the ideal of C_0.
     Let AA^N be the affine space with coordinate functions a_{i,j}.
     The unfolding equations define a subscheme F contained in AA^n x AA^N,
     whose fiber over 0 in AA^N is the curve C_0.",

     PARA{},

     "We then compute the ideal J defining the flattening stratum V(J) in AA^N
     containining 0, and restrict the family F to this stratum, so that
     the family becomes a family of curves in AA^n. By Pinkham's Theorem,
     the semigroup L is a Weierstrass semigroup if and only if some fiber C
     of this family is a non-singular affine curve, in which case the
     point with Weierstrass semigroup L is the unique point at infinity of the
     projective closure of C (in a suitable reembedding).",

     PARA{},

     "To make these computations efficient, we work over a large finite prime field
     but we wish to transfer the conclusions to characteristic 0, and thus to
     compact Riemann surfaces. For this purpose it suffices to lift a sub-family
     with smooth fiber to characteristic 0. For this purpose we would like to
     compute the flattening stratum using only a subset of the variables,
     and our hope is that the ML algorithms would help us choose a smaller,
     perhaps minimal set of variables that would do.",

     PARA{},

     "It is important to know that the rings AA^n and AA^N are graded.
     One of the data that we present is the ",
     TO optimalBound ,
     ", defined
     as the largest degree b (if any) such that there exists a family
     with smooth fiber involving only variables of degree > b.
     This depends only on L.",
     
     PARA{},
     
     "The next datum we present is the the ",
     TO optimalRange ,
     " which is
     a an interval {b+1..a} which is defined to be the smallest interval
     starting with b+1 such that there exists a family
     with smooth fiber involving only variables of degree between b+1 and a.
     This range depends only on L.",
     
     PARA{},
     
     "The third datum we produce are some lists that correspond to minimal
     sets of variables of degrees within the given range 
     are the positions minimal sets of variable such that there exists a family
     with smooth fiber involving only these variables. These may not be
     uniquely determined by L.",

     PARA{},
     
     "We assign each variable a_{i,j} an integer in the interval from 0
     to the total number of variables minus 1, by its position in the lexicographic
     using the pair {i,j}. We always refer to the variables by their positions,
     so that a minList is actually a list of positions, called
     in the program a positionList. Using the functions ",
     TO positionListToArray ,
     " and ",
     TO degreeArray,
     " which variables
     are in which positions.",

     PARA{},
     
     "The raw data that we present is in separate files on gitHub called
     boundsg, rangesg,minListsg, where in each case g is
     an integer >3, referring to the genus of the semigroups
     whose data is in the file.",
     
     PARA{},
     
     "The data in bounds6,
     for example, is a list of pairs (L,b), where L is the
     ordered list of minimal generators of the semigroup,
     and b is the optimal lower bound, as described above.",

     PARA{},

     "The data in ranges6 is a list of pairs (L,R), where L is the
     ordered list of minimal generators of the semigroup,
     and R is the optimal range, as described above. (This
     could be condensed to the triple (L,min R, max R).",

     PARA{},

     "The data in minLists6 is a list of lists: for each
     semigroup L there is a list containing one or more
     pairs of the form (L,minList).",
     

     SUBSECTION "Enhancing the Data",

     "Given the semigroup L, the minList data contains only
     the position of the variables used. Applying the function ",
     TO positionListToArray ,
     " yields a nested list sorting 
     the positions by the equation in which the corresponding
     variable occurs. ",
     TO degreeArray ,
     " applied to this
     position array, yields a nested list of the corresponding
     degrees.",
     PARA{},
     "Additional discrete data associated to the semigroup L
     is in the betti table of the minimal free resolution of
     semigroup ring, as a module over the coordinate ring of
     AA^n. A condensed version is given in the syzygy format
     obtained by ",
     TO syzFormat ,
     " L. These are the `total betti
     numbers' of the resolution. See ",
     TO dataForML,
     " which
     gives a visual presentation of these data.",
     PARA{},
     "We suggest that you begin by following the link to the documentation
     nodes ",
     TO dataForML, " and ",
     TO addData,
     ". The last function adds data to instances of our new examples of non Weierstrass semigroups.
     It would be interesting if an AI machine sees patterns in these data.",
     
}

-- combinatorial functions --

doc ///
Key
 apery
 (apery, List)
Headline
 Compute the apery set, multiplicity and conductor 
Usage
 A = apery L
Inputs
 L: List
  of positive integers
Outputs
 A:HashTable
Description
  Text
   The smallest nonzero element of s is the \emph{multiplicity}. The Apery set (really sequence) of a semigroup S is the
   the list {a_1..a_m-1} where a_i is the smallest element in s such that a_i = i mod m.
   The \emph{conductor} is 1 plus the largest element \emph{not} in S. We generally specify a semigroup by giving
   a list of positive integers L with gcd = 1, representing the semigroup of all sums of
   elements of L.
  Example
   L = {3,5}
   apery L
SeeAlso
  aperySet
///


doc ///
Key
 aperySet
 (aperySet, List)
 (aperySet, HashTable)
Headline
 Compute the apery set of a numerical semigroup
Usage
 as = aperySet L
 aS = aperySet HL 
Inputs
 L: List
  of positive integers
 H: HashTable
  as computed by H = apery L
Outputs
 aS: List
Description
  Text
   L is taken as generators of a numerical semigroup S; should have gcd = 1.
   The apery set is then the list aS = {a_1..a_(m-1)} where m is the smallest
   element of L, and a_i is the smallest element of S with a_i = i mod m.
  Example
   aperySet {3,5}
   semigroup {3,5}
SeeAlso
 apery
///


doc ///
Key
 semigroup
 (semigroup, List)
Headline
 Compute the semigroup generated by a list of positive integers
Usage
 L = semigroup L0
Inputs
 L0: List
Outputs
 L: List
Description
  Text
   The semigroup is actually computed by the function apery, and
   semigroup L = (apery L)#"semigroup"
  Example
   semigroup {5,4}
SeeAlso
   apery
///

doc ///
Key
 minimalSemigroupGens
 (minimalSemigroupGens, List)
Headline
 Find a minimal set of semigroup generators
Usage
 L' = minimalSemigroupGens L
Inputs
 L: List
  generators of a semigroup
Outputs
 L': List
  minimal generators of the same semigroup
Description
  Text
   The set of generators is minimal if it has empty
   intersection with the set of sums of non-zero generators.

   It would have been nicer to overload @TO mingens@ to
   accept a list.
  Example
   L = semigroup {3,7}
   minimalSemigroupGens L
SeeAlso
 semigroup
///


doc ///
Key
 semigroupRing
 (semigroupRing, List)
 [semigroupRing, BaseField]
Headline
 forms the semigroup ring over BaseField
Usage
 A = semigroupRing L
Inputs
 L:List
  of semigroup generators
Outputs
 A:Ring
  algebra over BaseField
Description
  Text
   If the basering is kk, the semigroup ring
   is A = kk[x^S] where x^S denotes the set of
   monomials in variables x_i with exponent
   vectors in S, and kk is the field that is the value
   of the option BaseField (ZZ/10007 by default).

   If m is the  multiplicity of S,
   the semigroup ring depends up to an
   isomorphism that may change the degrees,
   only on the face of the Kunz cone
   in which the semigroup lies.

   Semigroup rings are interesting as
   examples, and arise as Weierstrass semigroups
   of points on algebraic curves: if p in C
   is such a point, then the Weierstrass semigroup
   of C at p is the set of pole orders of rational
   functions with poles only at p, and the
   semigroupRing is the associated graded ring of the filtered ring
   $\bigcup_{n >= 0} H^0(O_C(np))$.
   For non-Weierstrass
   points the semigroup is 0,g+1,g+2.., and there are
   finitely many "Weierstrass" point p
   whose semigroup has weight >=2.

   For example if C is a smooth plane quartic,
   then at each ordinary flex point, the semigroup is
   0,3,5,6,7,..
   
  Example
   semigroupRing {3,4,5}
   weight {4,5,6,7}, gaps {4,5,6,7}
   semigroupRing {4,5,6,7}
   weight {3,5,7}, gaps {3,5,7}
   semigroupRing {3,5,7}
   weight {3,4}, gaps {3,4}
   semigroupRing({3,4}, BaseField => QQ)
SeeAlso
 semigroupIdeal
 weight
 ///
 
doc ///
Key
 semigroupIdeal
 (semigroupIdeal, List)
 [semigroupIdeal, "VariableName"=> "x"]
 [semigroupIdeal, "MinimalGenerators"=>true]
 [semigroupIdeal, BaseField]
Headline
 The ideal defining the semigroup ring
Usage
 I =  semigroupIdeal L
Inputs
 L: List
Outputs
 I: Ideal
Description
  Text
   The semingroup ideal of the semigroup generated by L
   is the kernel of the map kk[x_0..x_(#L)] -> kk[t]
   sending x_i to t^(L_i), where kk is the specified BaseField,
   defaulting to ZZ/101 and x is the specified VariableName.
   If the option "MinimalGenerators" is set to true, the default, then
   the program first computes a minimal set of generators from L;
   if it is set to false, the program uses L itself.
  Example
   semigroupIdeal {5,7}
   semigroupIdeal({5,7,10}, "MinimalGenerators" => false)
SeeAlso
 minimalSemigroupGens
 semigroupRing
///


 doc ///
Key
 type
 (type, List)
Headline
 type of the local semigroup ring
Usage
 r = type L
Inputs
 L:List
  of semigroup generators
Outputs
 r: ZZ
  the type
Description
  Text
   The type of a local Cohen-Macaulay ring is the number
   of generators of the canonical module, or equivalently the
   dimension of the socle of an zero-dimensional reduction.

   For example, the type of a complete intersection such as
   the semigroup ring of a semigroup generated by 2 elements.
  Example
   type {3,5}
SeeAlso
 socle
///

doc ///
Key
 socle
 (socle, List)
Headline
 elements of the semigroup that are in the socle mod the multiplicity
Usage
 s = socle L
Inputs
 L:List
  generators of a semigroup
Outputs
 s:List
  subset of the Apery set representing the socle mod the multiplicity
Description
  Text
   Let S = semigroup L
   be a numerical semigroup with minimal non-zero element m,
   and consider the artinian ring
   A(s) = k[{t^i : i in s]/(t^m).
   The socle of A(s) is the sum of the minimal nonzero ideals,
   and socle L is a set of generators of the socle
  Example
   L = {3,7}
   s = semigroup L
   socle L
   L = {3,4,5}
   s = semigroup L
   socle L
SeeAlso
 semigroup
///







doc ///
Key
 gaps
 (gaps, List)
Headline
 The gap sequence of a semigroup
Usage
 G = gaps L
Inputs
 L: List
  of semigroup generators
Outputs
 G: List
  the gap sequence
Description
  Text
   If semigroup L is the Weierstrass semigroup of a Riemann surface
   C at a point, then #gaps L = g = h^0(omega_C), the genus of C. Furthermore,
   the number of elements of sums(n, G) is bounded by the dimension of
   h^0(omega_C^n) = n*(2g-2)-g+1 = (2n-1)g-2n+1. However, for
   an arbitrary semigroup the number #sums(n,G) may be larger;
   the first such example was found by Ragnar Buchweitz, and
   is given below.

   The function isGapSequence returns either false or generators
   of the semigroup of which the sequence is the gap sequence.

  Example
   G=toList(1..12)|{19,21,24,25}
   g = #G
   for n from 1 to 3 list (#sums(n,G),n*(2*g-2) - g + 1)
   L=isGapSequence G
   G ==gaps L
Caveat
SeeAlso
 isGapSequence
 findSemigroups
///

doc ///
Key
 sums
 (sums, List, List)
 (sums, ZZ, List)
Headline
 sum of two sequences
Usage
 L = sums(L1, L2)
 L = sums(n,L1)
Inputs
 L1: List
 L2: List
 n:ZZ
Outputs
 L:List
Description
  Text
   sums(L1,L2) returns a sorted list of the unique
   sums of nonzero elements of L1 with L2;
   sums(n, L1) returns the sorted list of unique sums
   of n nonzero elements of L1.
  Example
   L1 = {2,3}
   L2 = {4,5}
   sums(L1, L2)
   sums(1, L1) == L1
   sums(L1, L1)
   sums(2,L1)
  Text
   Of course the sequence of arbitrary sums of elements including 0
   is essentially semigroup L. To get just the sums of n elements,
   one could write:
  Example
   n = 3
   {0}|sort unique flatten (for i from 1 to n list sums(i,L1))
///


doc ///
Key
 findSemigroups
 (findSemigroups, ZZ, ZZ, ZZ)
 (findSemigroups, ZZ, ZZ)
 (findSemigroups, ZZ) 
Headline
 Find all semigroups with a given number of gaps, multiplicity and/or conductor 

Usage
 LL = findSemigroups(mult, cond, numgaps)
 LL = findSemigroups(mult, numgaps)
 LL = findSemigroups(numgaps)  
Inputs
 mult: ZZ
  multiplicity
 cond: ZZ
  conductor
 numgaps: ZZ
  number of gaps
Outputs
 LL: List
  of sequences of generators of semigroups with the given invariants
Description
  Text
   If S is the Weierstrass semigroup of a point p on a Riemann surface X -- that
   is, the semigroup of pole orders of rational functions at p,
   then the genus of X is the number of gaps of S and there is a 
   differential on X vanishing to order exactly d iff d+1 is a gap.
  Example
   findSemigroups(5,14,8)
   G = gaps {5,7,9}
   #G
  Text
   The number of vanishing orders of quadratic differentials
   on is h^0(2K) = (4g-4) - g + 1 = 3g-3,
   so if s is the semigroup of pole orders of a point on X
   and G is the set of gaps, then there can be at most 3g-3 distinct
   sums of pairs of elements of G. This gives a nontrivial obstruction
   to the smoothability of the semigroup ring of S and thus to the
   existence of a Weierstrass point with semigroup s.

   The following semigroup, discovered by Ragnar Buchweitz (Thesis)
   was the was the first one to have been proven not
   to be Weierstrass.
  Example
   G=toList(1..12)|{19,21,24,25}
  Text
   The function @TO isGapSequence@ returns generators for
   the semigroups with given gap sequence or returns false if there is
   no such semigroup
  Example
   L=isGapSequence G
   g = #G
   3*g-3
   #sums(G,G)
SeeAlso
 isGapSequence
 gaps
///

doc ///
Key
 isGapSequence
 (isGapSequence, List)
Headline
 test whether a list of integers can be the list of gaps of a semigroup
Usage
 L = isGapSequence G
Inputs
 G: List
Outputs
 L:Boolean
 L:List
Description
  Text
   The function isGapSequence returns either false or
   a list of generators
   of the semigroup of which the sequence is the gap sequence.
   Note that the gap sequence of a semigroup of multiplicity m
   begins with 1..m-1, and ends with the Frobenius number c-1,
   where c is the conductor.
  Example
   G = {1,2,3,4,6,9,11,14}
   isGapSequence G
   G = {1,2,3,4,6,9,11}
   S = isGapSequence G
   G == gaps S
SeeAlso
 gaps
///

doc ///
Key
 syzFormat
 (syzFormat, Complex)
 (syzFormat, Ideal)
 (syzFormat, List)
Headline
 Total betti numbers of the semigroup ideal of L
Usage
 F=syzFormat L
Inputs
 L: List
  generators of a semigroup ring
Outputs
 b:List
  of the ranks modules in the free resolution of the semigroup ideal
Description
  Text
   The ranks of the modules, called format of the resolution by Weyman, is computed.
  Example
   L={6,9,11,14,16}
   syzFormat L
   res ideal semigroupRing L
References
  Weyman
SeeAlso

///


doc ///
Key
 buchweitzSemigroups
 (buchweitzSemigroups, ZZ)
 (buchweitzSemigroups, ZZ, ZZ)
 (buchweitzSemigroups, ZZ, ZZ, ZZ)  
Headline
 Finds semigroups that are not Weierstrass semigroups by the Buchweitz test
Usage
 LL = buchweitzSemigroups g
 LL = buchweitzSemigroups (m,g)
 LL = buchweitzSemigroups (m,c,g)
Inputs
 g:ZZ
  semigroupGenus
 m:ZZ
  multiplicity
 c:ZZ
  conductor
Outputs
 LL:List
  list of semigroups
Description
  Text
   Uses findSemigroups to produce lists of semigroups with the given
   invariants, and then uses the Buchweitz test: the following
   inequality holds for Weierstrass semigroups:
   sums(2, #gaps L) <= dim H^0(\omega_C^{2) = 2*(2g-1) - g + 1.
  Example
   B = buchweitzSemigroups (13,26,16)
   --buchweitz 0
   B = buchweitzSemigroups (14,28,17)
  Text
   The second example in these two cases are part of the sequence defined in @TO buchweitz@. As g increases
   there are many more; for example
   #buchweitzSemigroups (15,30,18) == 8
SeeAlso
 buchweitz
 findSemigroups
///

doc ///
Key
 weight
 (weight, List)
Headline
 weight of a semigroup
Usage
 w = weight L
Inputs
 L:List
Outputs
 w: ZZ
Description
  Text
   If S is the Weierstrass semigroup S of a point p on a Riemann surface C,
   then the vanishing sequence (v_0,\dots, v_(g-1)) of the canonical series at p
   is the list of orders of vanishing of differential forms at p, and the
   ramification sequence at p is (v_0 - 0, v_1 - 1, .. ,v_(g-1) - (g-1)).
   The weight of the Weierstrass point p is the sum of the ramification sequence at p.

   The vanishing sequence can be computed from the set G of gaps in S as
   v_i = G_i - 1, so the weight is sum(G_i - 1 - i) or as the number of pairs
   (a,b) such that a is in S, b is a gap, and a < b.

  Example
   weight {5,7}
   semigroup{5,7}
   gaps{5,7}
  Text
   The effective weight ewt is the number of such pairs where a is a minimal generator
   of S; this may be a better measure.
  Example
   minimalSemigroupGens{5,7}
   ewt {5,7}
SeeAlso
 minimalSemigroupGens
 gaps
 ewt
///

doc ///
Key
 ewt
 effectiveWeight
 (ewt, List)
 (effectiveWeight, List)
Headline
 Effective weight of a semigroup (Pflueger)
Usage
 w = ewt L
Inputs
 L: List
  generators of a semigroup
Outputs
 w: ZZ
  the effective weight
Description
  Text
    The effective weight of a semigroup S is defined as the number
   of pairs (a,b) such that a is a minimal generator of S and b is a gap of S with a<b.

   By contrast, the @TO weight@ of S (the sum of the ramification indices of the corresponding Weierstrass
   point) may be defined as the number of pairs (a,b) such that a is in S and b is a gap with a<b.

   Improving on work of Eisenbud-Harris (who proved that primitive semigroups S are Weierstrass),
   and occur in codimension equal to the @TO weight@ of S),
   Nathan Pflueger introduced the "effective weight" and showed that all semigroups with
   semigroupGenus g and effective weight w<g are Weierstrass, and occur on a subvariety of M_(g,1) with
   codimension w.

   For example, semigroups generated by two elements are always Weierstrass since
   complete intersections are smoothable; they are almost never primitive, 
  Example
   L = {6,7}
   semigroupGenus L
   weight L
   ewt L
References
 Pflueger, Nathan . On nonprimitive Weierstrass points.
 Algebra Number Theory  12  (2018),  no. 8, 1923- -1947.
SeeAlso
 semigroupGenus
///

doc ///
Key
 semigroupGenus
 (semigroupGenus, List)
Headline
 Compute the number of gaps (genus) of a semigroup
Usage
 g = semigroupGenus L
Inputs
 L: List
Outputs
 g: ZZ
Description
  Text
   gaps L is the list of the finitely many positive integers
   not in the semigroup generated by L.
  Example
   semigroupGenus {4,7}
   G = gaps {4,7}
   #G
   S = semigroup{4,7}
   set G + set S  == set(0..21)
SeeAlso
 gaps
 semigroup
///


doc ///
Key
 knownExample
 (knownExample, List)
Headline
 Is L a known Weierstrass semigroup?
Usage
 b = knownExample L
Inputs
 g:ZZ
  semigroupGenus
Outputs
 b:Boolean
  true if L is a known example of a Weierstrass semigroup
Description
  Text
   Certain semigroups are known to be Weierstrass. For example L has 2  or 3 generators only, by work of Pinkham and Sally. 
   Another sort examples are semigroup with small weight ewt(L) < semigroupGenus L by the work Nathan Pflueger extending
   work of Eisenbud-Harris.
  Example
   L={7,12,13}
   knownExample L
   L={7,8,9,11,13}
   ewt L, semigroupGenus L
   knownExample L
   LL=findSemigroups(9,10);#LL
   select(LL,L->not knownExample L)
   #oo
SeeAlso
  findSemigroups
///

-* commutative algebra functions *-

doc ///
Key
 checkFlatness
 (checkFlatness, Ideal,Ideal)
 [checkFlatness,Verbose]
Headline
 Check that the fiber and the semigroup ideal form a flat family
Usage
 b=checkFlatness(I,fiber)
Inputs
 I:Ideal
  ideal of a semigroup ring
 fiber: Ideal
  ideal of a fiber in a deformation
Outputs
 b:Boolean
Description
  Text
   The fiber is a deformation of the semigroup ring iff the one parameter homogenization
   of the fiber has the same betti table as I.
References

SeeAlso

///




doc ///
Key
 withRandomPoint
 withAffineBase 
 withComponents
 (withAffineBase, Ideal, Ideal ,Matrix)
 (withRandomPoint, Ideal, Ideal ,Matrix)
 (withComponents,  Ideal, List ,Matrix)
 [withRandomPoint,Verbose]
 [withRandomPoint,Probably]
 [withComponents,Verbose]
 [withComponents,Probably]
 [withAffineBase,Verbose]
 [withAffineBase,Probably]
Headline
 Compute the dimension of the singular locus of a random fiber 
Usage
 d=withAffineBase(I,J,family)
 d=withRandomPoint(I,J,family)
 d=withComponents(I,cJ,family)
Inputs
 I:Ideal
  ideal of a semigroup ring
 J: Ring
  ideal of flatness relations
 cJ: List
  list of components of the ideal J of flatness relations
 family: Matrix
  equations of the family
Outputs
 d: ZZ
  dimension of the singular loci of a random fiber
Description
  Text
   Depending on the nature of the ideal of flatness relations J the function computes
   the dimension of of the singular loci of a random fiber.
   If J=0, ie. , the base is an affine space, we simply choose a random point in the corresponding affine s
   space.
   
   If base V(J) is irreducible, then we use the function findPoint to find a random
   point in the base.

   If V(J) is reducible, then we find a point on each of ist components listed in cJ
   and return the minimum of the dimension of the singular loci of the fibers.
   With the options Verbose=>true the fuction prints these dimensions for each fiber.

   As an additional check we assert in all cases that the correponding fiber is a fiber
   in a one parameter flat family with the semigroup ring V(I) as special fiber.
  Example
   L={6, 8, 10, 11, 13}
   I=ideal semigroupRing(L,BaseField=>ZZ/nextPrime 10^4);
   (A,unfolding)=makeUnfolding I;
   b = semigroupGenus L-3; 
   as=apply(numgens I,i->a=drop(support unfolding_{i},#L));
   rL=apply(#as,i->select(as_i,m->(degree m)_0> b));
   restrictionList=apply(flatten rL,m->sub(m,A));
   (J,family)=getFlatFamily(I,A,unfolding,restrictionList);
   (J1,family1)=pruneFamily(I,J,family);
   cJ=decompose J1;
   assert(#cJ == 2)
   withComponents(I,cJ, family1,Verbose=>true) 

References
  
SeeAlso
  findPoint
///

     doc ///
       Key
        getFlatFamily
        -- (getFlatFamily, List, RR, ZZ) 
        -- for moved from AIWei
        (getFlatFamily, Ideal,Ring,Matrix)
        (getFlatFamily, Ideal,Ring,Matrix,List)
        -- end for moved from AiWei
        [getFlatFamily, BaseField]
        [getFlatFamily, Verbose ]
       Headline
        Compute the flat family depending on a subset of parameters of the universal unfolding
       Usage
        (J,family)=getFlatFamily(I,A,runfolding)
	(J,family)=(getFlatFamily(I,A,unfolding,variableList)
       Inputs
        I:Ideal
         of a semigroup ring
	A:Ring
	 coordinate ring of the base of the restricted unfolding
        runfolding:Matrix
	 equations of the restricted unfolding
        variableList: List
	 list of variables to be used in the restricted unfolding
       Outputs
        J: Ideal
	 ideal of flattening relations
	family: Matrix
	 equations of the reduced equations
       Description
        Text
	 We compute the flattening relations.
	Example
	 L = {4,5,6}
	 semigroupGenus L
	 I=ideal semigroupRing(L,BaseField=>ZZ/nextPrime 10^4)
	 (A,unfolding)=makeUnfolding I;
	 (J,family)=getFlatFamily(I,A,unfolding);
	 betti J
	 support unfolding
	 support family
	 family_(0,0)
	 gens ring family
	 --ramdomFiber(I,J,family)
	 support family
	 support family /degree
        Text
	 In the second version we restrict to a subset of the variables
	Example
	 b=optimalBound L
	 initialList=prepareInitialPositionList(L,b)
	 as = apply(numgens I,i-> drop(support unfolding_{i},#L))
         as1=apply(flatten as,m->sub(m,A))
	 restrictionList=as1_initialList
	 (J1,family1)=getFlatFamily(I,A,unfolding,restrictionList)
	 (J2,family2)=pruneFamily(I,J1,family1)
	 --isARandomFiberSmooth(I,J2,family2)
      SeeAlso
	 makeUnfolding
	 flatteningRelations
	 getFlatFamily
	 
    ///

     doc ///
       Key
        pruneFamily
        (pruneFamily,Ideal,Ideal,Matrix)
	[pruneFamily,Verbose]
       Headline
        Present the family with fewest number of variables
       Usage
        (J1,family1)=pruneFamily(I,J,family)
       Inputs
        I:Ideal
         of a semigroup ring
	J:Ideal
	 ideal of flattening relations of the family 
        family:Matrix
	 equations of the family
       Outputs
        J1: Ideal
	 pruned ideal of J
	family1: Matrix
	 equations of reduced family
       Description
        Text
	 If a generator of J has a variable as lead term then
	 this variable can be removed from the presentation of (ring J/J).
	 At the same time we remove this variable from the equations of
	 the family.	 
	Example
	 L={6, 8, 10, 11, 13}
	 I=ideal semigroupRing(L,BaseField=>ZZ/nextPrime 10^4);
	 (A,unfolding)=makeUnfolding I;
	 b = semigroupGenus L-3; 
	 as=apply(numgens I,i->a=drop(support unfolding_{i},#L));
	 rL=apply(#as,i->select(as_i,m->(degree m)_0> b));
	 restrictionList=apply(flatten rL,m->sub(m,A));
	 (J,family)=getFlatFamily(I,A,unfolding,restrictionList);
	 leadTerm J
	 (J1,family1)=pruneFamily(I,J,family);
	 leadTerm J1	 
      SeeAlso
	 makeUnfolding
	 flatteningRelations
	 getFlatFamily
	 prune
    ///


    
 -*
doc ///
Key
 isARandomFiberSmooth
 (isARandomFiberSmooth, Ideal, Ideal, Matrix)
 [isARandomFiberSmooth, BaseField]
 [isARandomFiberSmooth, Verbose ]
Headline
 Test whether a random fiber is smooth
Usage
 b=isARandomFiberSmooth(I,J1,family)
Inputs
 I: Ideal 
  semigroup ideal
 J1:Ideal
  flatness relations among the parameters
 family:Matrix
   a flat family
Outputs
 b: Boolean
   true if a random fiber is smooth, false otherwise
Description
  Text    
    We check whether a random fiber over a random closed point of each component of  J1 is smooth.
    If we find a smooth fiber we return true, else we return false.
  Example
    L={6,8,10,11}
    semigroupGenus L
    (I,J1,family)=getFlatFamily(L,0.30,0);
    isARandomFiberSmooth(I,J1,family)
    SA=ring family
    transpose family
SeeAlso
    makeUnfolding
///
*-

doc ///
Key
 dimSingularLocusOfFiber
 (dimSingularLocusOfFiber, Ideal)
 [dimSingularLocusOfFiber, Probably]
Headline
 Test whether a random fiber is smooth
Usage
 d=dimSingularLocusOfFiber(fiber)
Inputs
 fiber: Ideal 
  ideal of a fiber in a flat family of affine curves
Outputs
 d: ZZ
   dimension of the singular locus of the fiber
Description
  Text    
    We compute the dimension of the singular locus of the fiber. With the option Probably=>true
    we use the function regularInCodimension from the fastMinor package. In that case we return 0
    in case the fiber the probalistic function regularInCodimension did not prove smoothness.
    In case the function returns -1, the fiber is definitly smooth.
  Example
    L={6,9,13,14}
    I=semigroupIdeal L
    degrees source gens I
    g = semigroupGenus L
    fiber=getFiber(L,14)
    dimSingularLocusOfFiber(fiber)
    radical ideal singularLocus fiber
    b=optimalBound(L,13,Probably=>true)
    fiber=getFiber(L,b)
    dimSingularLocusOfFiber(fiber,Probably=>true)
///

doc ///
Key
 getFiber
 (getFiber, List ,ZZ)
 (getFiber, List, List)
 [getFiber,Verbose]
Headline
 Get a random fiber.
Usage
 fiber=getFiber(L,b)
 fiber=getFiber(L,positionList)
Inputs
 L: List 
  generators of a semigroup
 b: ZZ
  lower bound for the degree of the unnfolding parameters
Outputs
 fiber: Ideal
   a random fiber of the truncated family
Description
  Text    
    We randomly choose a fiber of the flat family associated to
    the degree truncate restricted unfolding.
  Example
    L={6,8,10,11}
    semigroupGenus L
    b=optimalBound L
    fiber=getFiber(L,b)
    dimSingularLocusOfFiber(fiber)
    fiber=getFiber(L,b+1)
    dimSingularLocusOfFiber(fiber)
    radical ideal singularLocus fiber
  Text
    In the second we restrict to a subset of the unfolding
    variables specified by the positionList.
  Example
    L={6,8,10,11}
    semigroupGenus L
    initialList=prepareInitialPositionList(L,Verbose=>true)
    positionList={0,7,8,18,30}
    fiber=getFiber(L,positionList)
    dimSingularLocusOfFiber fiber
    radical ideal singularLocus fiber
    positionList={0,7,8,18,27,30}
    fiber=getFiber(L,positionList)
    dimSingularLocusOfFiber fiber
    radical ideal singularLocus fiber
SeeAlso
    dimSingularLocusOfFiber
    prepareInitialPositionList
///








doc ///
Key
 def1
 (def1, List)
 [def1,BaseField]
Headline
 degrees of a basis of T^1
Usage
 D = def1 L
Inputs
 L: List
  generators of a semigroup
Outputs
 D: List
  degrees of a basis of T^1(semigroupRing L)
Description
  Text
   T^1(B) is the tangent space to the versal deformation of
   the ring B, and is finite dimensional when B has isolated
   singularity. If B = S/I is a Cohen presentation, then
   T^1(B) = coker Hom(Omega_S, B) -> Hom(I/I^2, B).
   When B is a semigroup ring, then Henry Pinkham proved that
   an open subset of the space of elements of T1 of
   negative degree correspond to smoothings of the projective cone
   of the semigroup ring to Riemann surfaces
  Example
   def1{2,3}
///

doc ///
Key
 buchweitzCriterion
 (buchweitzCriterion, List)
 (buchweitzCriterion,ZZ,List)
Headline
 Does L satisfies the Buchweitz criterion?
Usage
 d = buchweitzCriterion L
 d = buchweitzCriterion(m,L)
Inputs
 L:List
  generators of a semigroup or the aperyset of a semigroup
 m:ZZ
  the multiplicity of the semigroup
Outputs
 d:ZZ
Description
  Text
   A Weierstrass semigroups L satisfies

       3*(semigroupGenus L-1) -#sums(G,G) >=0.

   The function returns this difference.  

  Example
   L={7,12,13}
   buchweitzCriterion L
   L= buchweitz 0
   buchweitzCriterion L
SeeAlso
  buchweitz
///


doc ///
Key
 makeUnfolding
 (makeUnfolding, Ideal)
 (makeUnfolding, List) 
 [makeUnfolding, BaseField]
 [makeUnfolding, Verbose ]
Headline
 Makes the universal homogeneous unfolding of an ideal with positive degree parameters
Usage
 (A,unfolding) = makeUnfolding I
 (A,unfolding) = makeUnfolding sgrp
Inputs
 I:Ideal
 sgrp:List
  generators of a semigroup
Outputs
 A: Ring
   algebra of unfolding parameters
 unfolding: Matrix
   equations of the unfolding
Description
  Text
   Given a (quasi)homogeneous ideal in a ring S = kk[x_0..x_n]
   the function creates a positively graded polynomial ring A = kk[a_{i,j}]
   and computes the unfolding of I as an ideal 
   of SA = kk[x_0..x_n, a_{i,j}]. This can be used as a step in computing the
   semi-universal deformation of the affine cone defined by I.

   In the case of

   makeUnfolding sgrp

   the routine first forms the ideal of the semigroup ring, and applies makeUnfolding to this.
  Example
   L={4,5,7}
   I := semigroupIdeal L;
   (A,unfolding):= makeUnfolding I;
   S=ring I
   fI=res I
   degs=flatten (gens A/degree)
   n=floor(max degs/2+3)
   restricted=ideal select(gens A, y-> (degree y)_0<n);
   SA=ring unfolding
   runfolding=unfolding%sub(restricted,SA);
   transpose runfolding
   J=flatteningRelations(I,A,runfolding);
   cJ=decompose J;#cJ
   ideal prune (A/J)
   family=runfolding%sub(J,SA);
  Text
   This is a flat family!
  Example
   betti res ideal family == betti res I
   fiber=ideal sub(family,vars S|random(S^1,S^(numgens A)));
   singFiber=radical ideal gens gb (fiber+minors(codim I,jacobian fiber))
  Text
   Thus the family is a smoothing of S/I so
   the semigroup L in the example is a Weierstrass semigroup by Pinkham's thesis.
SeeAlso
 flatteningRelations
///

doc ///
Key
 flatteningRelations
 (flatteningRelations, Ideal, Ring, Matrix)
Headline
 Compute the flattening relations of an unfolding
Usage
 J= flatteningRelation(I,A,unfolding)
Inputs
 I:Ideal
  homogeneous with respect to a possibly nonstandard NN-grading
 A: Ring
  the ring of parameters of the unfolding
 unfolding: Matrix
  an unfolding of gens I
Outputs
 J: Ideal
   of A
Description
  Text
   Given the tuple (I,A,unfolding) the function computes the flattening relations
   via the set of Buchberger test syzygies.
   The procedure terminates since the parameters
   of A have positive degree, and the unfolding is homogeneous.
  Example
   L={4,6,7}
   I = trim semigroupIdeal L;
   (A,unfolding)=makeUnfolding I
   S=ring I
   fI=res I
   degs=flatten (gens A/degree)
   n=floor(max degs/2)+3
   restricted=ideal select(gens A, y-> (degree y)_0<n);
   SA=ring unfolding
   runfolding=unfolding%sub(restricted,SA);
   transpose runfolding
   J=flatteningRelations(I,A,runfolding);
   cJ=decompose J;#cJ
   ideal prune (A/J)
   family=runfolding%sub(J,SA);
   betti res ideal family == betti res I
  Text
   Thus this is a flat family!
  Example
   fiber=ideal sub(family,vars S|random(S^1,S^(numgens A)));
   singFiber=radical ideal gens gb (fiber+minors(codim I,jacobian fiber))
  Text
   Thus the family is a smoothing of S/I so
   the semigroup L in the example is a Weierstrass semigroup by Pinkham's thesis.

SeeAlso
 makeUnfolding
 ///

doc ///
Key
 findPoint
 (findPoint, Ideal)
 [findPoint, Verbose ]
Headline
 Find a kk-rational point in a variety
Usage
 point=findPoint c
Inputs
 I:Ideal
Outputs
 B: Matrix
   coordinates of a point in the finite ground field
Description
  Text 
   Given ideal c the functions adds random linear equations L to c to obtain
   1-dimensional ideal. Since the ground field is finite, decompose the ideal c+L
   will lead to a point with positive probability. Thus repeating will lead to success.
  Example
    kk=ZZ/101
    R=kk[x_0..x_6]
    c=ideal random(R^1,R^{2:-1,2:-2})
    B=findPoint c
    sub(c,B)==0

  
///





     doc ///
     Key
      testWeierstrass
      (testWeierstrass,List,ZZ)
      (testWeierstrass,List,List)
      (testWeierstrass,Ideal,Ring,Matrix)
      [testWeierstrass,Verbose]
      [testWeierstrass,Probably]
     Headline
      possibly show that a semigroup is Weierstrass
     Usage
      answer = testWeierstrass (L, bound)
      answer = testWeierstrass (L, positionList)
      answer = testWeierstrass (I, A, runfolding)     
     Inputs
      L:List
       semigroup generators
      bound : ZZ
      positionList : List
       list of positions of unfolding variables used for the restricted unfolding
      I : Ideal
       ideal of the semigroup ring
      A : Ring
       coordinate ring of the base of a the restricted unfolding runfolding
      runfolding: Matrix
       entries generate the ideal of a restricted unfolding
     Outputs
      answer : ZZ
       dimension of the singular locus of a fiber in a family
     Description
       Text
        If the input is (L,bound) the function restricts the universal
	unfolding to variables with degree > bound. It first
	computes I,A,runfolding as described above.

	Uses Gr\"obner bases to compute the flattening relations J \subset A.
	The routine chooses
	a random point in each component of the flattening locus V(J)
	and computes the singular locus of the fibers over these
	points. It returns the minimum of the dimension of the singular loci,
	thus 0 if all are singular and -1 if at least one in nonsingular.
	By Pinkham's theorem, if the output is -1 then the semigroup
	generated by L, or the semigroup L generated by the degrees
	of the generators of I, is a Weierstrass.
	semigroup.
       Example
        L = {5,7,9}
	g = semigroupGenus L
	bound = g-3
	testWeierstrass (L, bound)
	bound = 13
	testWeierstrass (L, bound, Verbose=>true)
	bound = 20
	testWeierstrass (L, bound, Verbose=>true)
       Text
	with bound = 20 the size of the flattening family is one point,
	whose fiber is the original semigroup ring, so there
	cannot be a nonsingular fiber.

	For the third form of the function, it is necessary to
	specify a large prime, to prevent accidents.
       Example
        L = {5,7,9}
        p = nextPrime 10^4
        I = semigroupIdeal(L, BaseField => ZZ/p)
        (A,unfolding) = makeUnfolding I;
	numgens A
	positionList=toList(0..10)|toList (12..18)
        (A',runfolding)=restrictedUnfolding(I,positionList)
        testWeierstrass(I,A',runfolding)
        positionList = {0,1}
        (A',runfolding)=restrictedUnfolding(I,positionList)
        testWeierstrass(I,A',runfolding, Verbose => true)
      Text
       The second version is a simpler to used version of the third 
      Example
       positionList=prepareInitialPositionList L
       testWeierstrass(L,positionList)
       finalList=systematicShrinking(L,positionList,Verbose=>true)
       testWeierstrass(L,finalList)
       (J,family,runfolding,J1)=showRestrictedFamily(L,finalList); 
       SB= ring runfolding
       sub(family,SB)==(runfolding%sub(J1,SB))
       J, J1
       transpose family ,transpose runfolding
     SeeAlso
      prepareInitialPositionList 
   ///

doc ///
Key
 restrictedUnfolding
 (restrictedUnfolding, Ideal, List)
Headline
 Compute a restricted unfolding
Usage
 (A,runfolding)=restrictedUnfolding(I,positionList)
Inputs
 I:Ideal
   ideal of semigroup ring
 positionList:List
   list of positions of the unfolding parameters to be used in the restricted unfolding
Outputs
 A: Ring
   coordinate ringof the restricted unfolding
 runfolding: Matrix
   equations of the restricted unfolding
Description
  Text 
   Given ideal c the functions adds random linear equations L to c to obtain
   1-dimensional ideal. Since the ground field is finite, decompose the ideal c+L
   will lead to a point with positive probability. Thus repeating will lead to success.
  Example
   L={6, 8, 10, 11, 13}
   I=ideal semigroupRing(L,BaseField=>ZZ/nextPrime 10^4);
   (A,unfolding)=makeUnfolding I;
   gens A/degree
   numgens A
   positionList=toList(0..40)
   (A,runfolding)=restrictedUnfolding(I,positionList)
   assert(testWeierstrass(I,A,runfolding) == -1)
   (J,family)=getFlatFamily(I,A,runfolding)
   support runfolding
   support family
///


doc ///
Key
 optimalBound
 (optimalBound, List, ZZ)
 (optimalBound, List)
 [optimalBound, Verbose]
 [optimalBound, Probably]
Headline
 Compute the largest bound for degree restriction
 
Usage
 b=optimalBound L
 b=optimalBound(L,guess)
Inputs
 L: List
  generators of a semigroup ring
 guess:ZZ
  a guess near the optimal bound
Outputs
 b:ZZ
  the optimal bound
Description
  Text
   Computes the largest integer b such that the restriction of the universal unfolding
   to base variable of degree > b leads to a flat family with random smooth fiber.
   In other words: L is a Weierstrass semigroup.
  Example
      L = {5,6,7}
   elapsedTime b=optimalBound(L,Verbose=>true)
   testWeierstrass(L,b+1)==0 and testWeierstrass(L,b)==-1
  Text
   Computes the largest integer b such that the restriction of the universal unfolding
   to base variable of degree > b leads to a flat family with random smooth fiber.
   In other words: L is a Weierstrass semigroup.
  Example
   L={5,6,7}
   elapsedTime b=optimalBound(L,12,Verbose=>true,Probably=>true)
   testWeierstrass(L,b+1)==0 and testWeierstrass(L,b)==-1
References
  
SeeAlso

///


doc ///
Key
 optimalRange
 (optimalRange, List, ZZ)
 [optimalRange, Verbose]
 [optimalRange, Probably]
 [optimalRange, Bisection]
Headline
 Compute the largest bound for degree restriction
 
Usage
 range=optimalRange(L,guess)
Inputs
 L: List
  generators of a semigroup ring
 guess:ZZ
  a guess near the optimal lower bound
Outputs
 range:List
  an optimal range of degrees
Description
  Text
   Starting with b=optimalBound L, the function computes the smallest a such that the range
   toList(b+1..a) detects that L is Weierstrass
  Example
   L = {5,6,7}   
   semigroupGenus L
   guess=12
   elapsedTime b=optimalBound(L,guess,Verbose=>true,Probably=>true)
   testWeierstrass(L,b+1)==0 and testWeierstrass(L,b)==-1
   elapsedTime range=optimalRange(L,guess,Verbose=>true)
   testWeierstrassRange(L,range)==-1
   posList=prepareInitialPositionList(L,range)
   netList degreeArray(L,positionListToArray(L,posList))
   elapsedTime finalPos=systematicShrinking(L,posList,Verbose=>true,Probably=>true)
   netList degreeArray(L,positionListToArray(L,finalPos))
   displayMinimalFamilies({{L,finalPos}})
References
  
SeeAlso
  testWeierstrass
  testWeierstrassRange
  degreeArray
  systematicShrinking
  displayMinimalFamilies
///


doc ///
Key
 testWeierstrassRange
 (testWeierstrassRange, List, List)
 [testWeierstrassRange, Verbose]
 [testWeierstrassRange, Probably]
Headline
 Compute the largest bound for degree restriction
 
Usage
 d=testWeierstrassRange(L,range)
Inputs
 L: List
  generators of a semigroup ring
 range:List
  a range of degrees
Outputs
 d:ZZ
  the dimension of the singular locus of a random fiber of the corresponding family
Description
  Text
  Example
   L={6, 8, 9, 10}
   semigroupGenus L
   guess=12
   elapsedTime range=optimalRange(L,guess,Verbose=>true)
   testWeierstrassRange(L,range)==-1
   range'=drop(range,1),testWeierstrassRange(L,range')
   range''=drop(range,-1),testWeierstrassRange(L,range'')
References
  
SeeAlso
  testWeierstrass
  testWeierstrassRange
///

doc ///
Key
 prepareInitialPositionList
 (prepareInitialPositionList, List)
 (prepareInitialPositionList, List, ZZ)
 (prepareInitialPositionList, List,List)   
 [prepareInitialPositionList, Verbose]
 [prepareInitialPositionList, Probably]
Headline
 Prepare an intitial position List
 
Usage
  initialList=prepareInitialPositionList(L)
  initialList=prepareInitialPositionList(L,b)
  initialList=prepareInitialPositionList(L,range)
Inputs
 L: List
  generators of a semigroup ring
 b: ZZ
  degree bound for the truncation
 range: List
  a range of degrees for for the variables in the desired restricted unfolding,
  possibly a nested List of List, in which case the range refers to a range of restricted unfolding
  parameters for each equations
Outputs
 initialList:List
  the positions of the unfolding variables in the truncation
Description
  Text
   In the first version we
   compute the largest integer b such that the restriction of the universal unfolding
   to base variable of degree > b leads to a flat family with random smooth fiber.
   We return the positions of these variables within the list of all unfolding parameters.
   In the second version we take all unfolding variables of degree larger than b.
   In the third version we take all variables with degree in the indicated range.
   With L={5,7,8,11} this example is slow, so we take a simpler one
   Example
   L = {5,9,13}
   elapsedTime initialList=prepareInitialPositionList(L,Verbose=>true)
   elapsedTime finalList=systematicShrinking(L,initialList,Verbose=>true)
   (J,family,runfolding,J1)=showRestrictedFamily(L,finalList); 
   J, J1
   transpose family,transpose runfolding,
   support family,support runfolding
   netList positionListToArray(L,finalList)
   netList positionListToArray(L,initialList)
  Text
   In the second version we take all unfolding variables of degree larger than b.
  Example
   L = {5,9,13}
   g=semigroupGenus L
   initialList=prepareInitialPositionList(L,g,Verbose=>true)
   testWeierstrass(L,initialList)
  Text
   In the third version we take all variables with degree in the indicated range.
  Example
   range={5,7,8}
   range = {30}
   initialList=prepareInitialPositionList(L,range,Verbose=>true)
   elapsedTime testWeierstrass(L,initialList)
   elapsedTime finalList=systematicShrinking(L,initialList,Verbose=>true)
   range1=degreeArray(L,positionListToArray(L,finalList,Verbose=>true))
   initialList1=prepareInitialPositionList(L,range1,Verbose=>true)
   elapsedTime finalList=systematicShrinking(L,initialList1,Verbose=>true)
SeeAlso
  showRestrictedFamily
  systematicShrinking
  positionListToArray
///

doc ///
Key
 showRestrictedFamily
 (showRestrictedFamily, List, List)
Headline
 Show the restricted family
 
Usage
  (J,family,runfolding,J1)=showRestrictedFamily(L,finalList)
Inputs
 L: List
  generators of a semigroup ring
 finalList: List
  a postion list of the unfolding parameters which are used in the restricted unfolding 
  
Outputs
 J:Ideal
  ideal of flattening relations of the family
 family: Matrix
  equations of the family
 runfolding: Matrix
  equations of the restricted unfolding
 J1: Ideal
  of flattening relation for the restricted unfolding
Description
  Text
   We present the flattening relations of the pruned family obtained form
   the restricted unfolding
   together with the equations of the pruned family.
   J1 and runfolding are the same data for the family before pruning, as a comparison.
  Example
   L={5,7,8,11}
   semigroupGenus L
   initialList=prepareInitialPositionList(L,Verbose=>true)
   finalList=systematicShrinking(L,initialList,Verbose=>true)
   (J,family,runfolding,J1)=showRestrictedFamily(L,finalList); 
   J, J1
   transpose family,transpose runfolding,
   support family,support runfolding
   netList positionListToArray(L,finalList)
   netList positionListToArray(L,initialList)
References
  
SeeAlso
  prepareInitialPositionList
  systematicShrinking
  positionListToArray
  pruneFamily
///

doc ///
Key
 liftToCharacteristicZero
 (liftToCharacteristicZero,List, Matrix,Ideal)
 [liftToCharacteristicZero,Verbose]
Headline
 lift to characteristic zero
Usage
  answer=liftToCharaceristicZero(L,family,J)
Inputs
 L: List
   the genertors of a semigroup
 family: Matrix
   the equations of a deformations over a finite prime field ZZ/p, typically p=10007
  J:Ideal
   the flattening relations over that field
Outputs
 answer:Boolean
  true if the resolution of the semigroup ideal lifts to a resolution of the family
Description
  Text
    If the coefficients in of the family and the generators of the ideal J are represented by integers which are in absolute value
    small compared to p, then we can regard these equations as equations over ZZ,
    and may consider the ring SAQQ=QQ[support family,Degree=>support family/degree]
    and substitute that family and the ideal J into SAQQ. The family extends to characteristic zero
    if the betti table of the resolution of the ideal generated by the substituted family
    over the ring SAQQ/sub(J,SAQQ) has the same betti table as the semigroup ideal ideal.
    Todo: maybe improve the code to work over Spec ZZ[1/f] for a small factor f)
  Example
   (L,positionList)=({6, 8, 10, 13, 15},{9, 19, 29, 42, 57, 59, 72, 90, 92, 110, 113});
   semigroupGenus L
   (J,family,rUnfolding,J1)=showRestrictedFamily(L,positionList);
   J
   transpose rUnfolding
   liftToCharacteristicZero(L,family,J)
   References
  
SeeAlso
  showRestrictedFamily
///



doc ///
Key
 displayMinimalFamilies
 (displayMinimalFamilies, List)
 [displayMinimalFamilies,Verbose]
Headline
 Display minimal families 
Usage
  displayMinimalFamilies(tD)
Inputs
 tD: List
  of training data of the form {L,minimalList}
  where the list L generates a semigroup and minimalList is a positionList
Outputs
 :Net
  a Net collecting some information
Description
  Text
   We collect in a Net for each example D in tD,
   
       the semigroup D_0
       
       the support of the final family

       the degrees of the variables of the final family
       
       the flattening relations of the family
       
       the number of variables eliminate by passing from the restricted unfolding
       
       the equations of the family       
  Example
   tD={({6, 8, 10, 11, 13},{10, 32, 55, 74, 85, 102}), ({6, 8, 9, 10},{11, 20, 32}), ({6, 7, 8,
      17},{2, 30, 40, 43, 44, 46, 60, 61, 86, 87, 89})};
   #tD
   displayMinimalFamilies tD
References
  
SeeAlso
  prepareInitialPositionList
  systematicShrinking
  positionListToArray
///

doc ///
Key
 systematicShrinking
 (systematicShrinking, List, List)
 [systematicShrinking, Verbose]
 [systematicShrinking, Probably]
Headline
 Compute a (locally) minimal list of unfolding parameter whose flattening has a random smooth fiber 
 
Usage
  finalList=systematicShrinking(L,initialList)
Inputs
 L: List
  generators of a semigroup ring
 initialList:List
  the positions of the unfolding variables with smooth fiber
Outputs
 finalList:List
  the positions of the unfolding variables with a minimal set of unfolding parameters
Description
  Text
   Starting with unfolding parameters corresponding to the initialList, we drop one of the variables
   at a time as long as the shrinked unfolding leads to a family with random smooth fiber.
  Example
   L={5,7,8,11}
   semigroupGenus L
   syzFormat L
   initialList=prepareInitialPositionList(L,Verbose=>true)
   finalList=systematicShrinking(L,initialList,Verbose=>true)
   (J,family,runfolding,J1)=showRestrictedFamily(L,finalList); 
   J, J1
   transpose family,transpose runfolding,
   support family,support runfolding
   netList positionListToArray(L,finalList)
   netList positionListToArray(L,initialList)
References
  
SeeAlso
  syzFormat
  showRestrictedFamily
  prepareInitialPositionList
  positionListToArray
///

doc ///
Key
 shrinkRange
 (shrinkRange, List, List)
 [shrinkRange, Verbose]
Headline
 Compute a (locally) minimal degree list for unfolding parameter whose flattening has a random smooth fiber 
 
Usage
  newRange=shrinkRange(L,range)
Inputs
 L: List
  generators of a semigroup ring
 range:List
  a range, ie., a lists of degrees of variables in a resticted unfolding with a smooth random fiber
Outputs
 newRange:List
   a sublist of range, which corresponds to minimal lists of degrees of variables in a resticted unfolding with a smooth random fiber
Description
  Text
   We delete successivly delete degrees d wih min range < d < max range
   and test wether we get family with smooth random fiber.
   Because the execution is slow, we simply report the results.
  Example
   L = {4,6,9,11}
   "elapsedTime range = optimalRange(L, 8) -- 10.6221s elapsed"
   range = {8, 9, 10, 11, 12, 13, 14}
   "elapsedTime newRange = shrinkRange(L, range) -- 5.72711s elapsed"
   newRange = {8, 11, 14}
  Text
   Using shrinkRange sometimes speeds up the search
   for minimal position lists:
   in fact
   They each yield just 1 posList:
  Example
   "elapsedTime minimalPositionLists(L,range,2)   -- 101.823s elapsed"
   "elapsedTime posLists = minimalPositionLists(L,newRange,2) -- 32.6299s elapsed"
  Text
   They each yield just one position list, in this case:
  Example
   posLists =  {{1, 2, 10, 11, 22, 33, 45, 46, 47, 59, 60}}
   elapsedTime testWeierstrassRange(L,{8,11,14})
   displayMinimalFamilies    {(L,posLists_0)}
SeeAlso
  minimalPositionLists
  systematicShrinking
///




doc ///
Key
 minimalPositionLists
 (minimalPositionLists, List, List, Number)
 [minimalPositionLists, Verbose]
 [minimalPositionLists, Probably]
Headline
 Compute a few (locally) minimal lists of unfolding parameters whose flattening has a random smooth fiber 
 
Usage
  minLists=minimalPositionLists(L,range,n)
Inputs
 L: List
  generators of a semigroup
 range:List
  a list of degrees to which to restrict the  unfolding variables
Outputs
 minList:List
   a list of minimal positionsLists specifying sets of unfolding variables that are sufficient for smoothing
Description
  Text
    We call a list of unfolding parameters (or positions of these in the list of all unfolding parameters)
    minimal if dropping any of the variables will no longer lead to a flat family with general smooth fiber.

    Given a range of degrees we first compute the positions posList of the unfolding parameters with those degrees
    and compute the corresponding restricted unfolding and its ideal J of @TO flatteningRelations@.
   
    We then remove from posList the positions whose corresponding variables are zero modulo the flattening relations J.
    In a second step we collect variables which if dropped no longer give smooth fibers.
    Finally we remove one by one remaining  variables until no variable can be removed without producing
    a family whose generic fibers are not smooth.
    The resulting set of variables is minimal in the above sense.

    Which variables are removed depends on the order of the elements in the position list. We try n permutations of this list,
    The first is the natural order, the second it reverse and all further come from a random permutation.
    This produces up to n different lists.
   
  Example
    L = {3,10,11}
    range = {10,11}
    minimalPositionLists(L, range, 2, Verbose => false)
    testWeierstrassRange(L,range) == -1
  Text
   This shows that there is a smooth fiber in the family defined by the list range.
  Example
    elapsedTime minLists = minimalPositionLists(L,range, 3,
	                                       Probably=>true)
  Text
   Each of the lists in the output is a minimal list of positions.
  Example
    tally apply(minLists,fL->#fL)
    netList apply(minLists,finalList->(
	(J,family,runfolding,J1)=showRestrictedFamily(L,finalList);
	netList {{support family}, {J},{transpose family}})
    )
  Text
    In this case we found two different minimal families within the given range.
SeeAlso
  prepareInitialPositionList
  showRestrictedFamily
///



doc ///
Key
 produceData
 produceBounds
 produceRangesFromBounds
 produceShrinkedRangesFromRanges
 produceMinListsFromRanges
 continueComputation
 (produceData, List,String)
 (produceData, List,ZZ,String)
 (produceBounds, List,String)
 (produceRangesFromBounds, List,String)
 (produceMinListsFromRanges, List,ZZ,String)
 (produceShrinkedRangesFromRanges, List,String)
 (produceMinListsFromRanges, List,ZZ,String)
 (continueComputation,Function,List,String)
 (continueComputation,Function,List,ZZ,String)
 [produceData, Verbose]
Headline
 Compute training data
Usage
  tD=produceData(LL,name)
  tD=produceData(LL,n,name)
  tB=produceBounds(LL,name)
  tR=produceRangesFromBounds(tB,name)
  tSR=produceShrinkedRangesFromRanges(tR,name)
  tL=produceMinListsFromRanges(tR,n,name)
  tY=continueComputation(F,tX,name)
  tL=continueComputation(produceMinListsFromRanges,tR,n,name)
Inputs
 LL: List
  a list of semigroups
 n:ZZ
  the number of desired minimal position lists
 name: String
 F: Function
   one of the five "produce" functions above
Outputs
 tD: List
   a list of pairs (L,data) with L a semigroup and data an optimalBound,
   an optimalRange or a minimal position list for L
Description
  Text
    We call a list of unfolding parameters (or positions of these in the list of all unfolding parameters)
    minimal if dropping any of the variables will no longer lead to a flat family with general smooth fiber.
    
    We compute such data from a semigroup L in four steps:
    
    1) We compute the optimal bound b, ie., the smallest integer b>-1 such
       that the resriction of the universal unfolding to parameters of degree >b
       leads to a flat family which a random smooth fiber. If no such b exists then
       L is probably not a Weierstrass semigroup.
    
    2) Given an optimal bound b we compute the smallest range of degree
       range=toList(b+1..d) such the restriction of the universal family to
       parameters of degrees in this range has a random smooth fiber.
    
    3) Given an range we compute a smallest shrinked range of degrees
       in the given range such the restriction of the universal family to
       parameters of degrees in this shrinked range still has a random smooth fiber.
    
    4) We successively drop parameters in the shrinked range until no more
       variable can be dropped and still get a random smooth fiber.
       We call such a smallest list a minimal list of unfolding parameters.
    
    In practise we specify these parameters by a position list corresponding
    to the order of the variables in the universal unfolding.
    
    Which minimal lists we obtain depends on the order in which we try to drop variables
    in step 4. A permutation of the variables can lead to different minimal list.
    
    On the other hand the optimal bound, the optimal range and the shrinked range is uniquely
    determined by L.  
    
    With the functions above we compute these data for a list LL of semigroups L.
    The output is a list of pairs (L,data) where data is an optimal bound, an optimal range, a
    shrinked range 
    or a minimal position list.
    
    Since the computation are expensive, we save this information also to the disk
    to a file with specified name. We then can continue the computations with
    the still todo instances to obtain a complete list of data.
    The data lists are fairly small.
  Example
    LL=select(findSemigroups 4,L->#L>2);#LL
    LL=reverse sort(LL,L->ewt L);
    apply(LL,L->(ewt L,L))
    LL=LL_{0,1};#LL
    name="tmp"
    tD=produceData(LL,name)
  Text
    We can recover tD from the file "name" on the disk:
  Example
    td=flatten getFromDisk name
    tD==td
    run "rm tmp"
  Text
    We can arrive at the same data using 3 functions.
  Example
    name="tempB"
    tB=produceBounds(LL_{0},name)
    continueComputation(produceBounds,LL,name)
    tb=getFromDisk name
  Text
    Above we only computed part of the result. Continuing got us the whole
    information. The same could be done by interupting a long M2 session
    and continueComputation after a restart.
  Example
    name="tempR"
    tR=produceRangesFromBounds(tb,name)
    name="tempL"
    tL=produceMinListsFromRanges(tR_{0},3,name)
    displayMinimalFamilies flatten tL
  Text
    Continuing gives the complete answer as produced by produceData above.
  Example     
    F=produceMinListsFromRanges
    continueComputation(F,tR,3,name)
    tD=getFromDisk name
    displayMinimalFamilies flatten tD
    run "rm tempB tempR tempL"
  Text
    The default value for "n" in continuing of produceMinListsFromRanges is three.
    In this particular
    case all three minimal lists coincide (up to pemutation). So we see only one for each semigroup.

SeeAlso
   displayMinimalFamilies
   degreeArray
   positionListToArray
   getFromDisk
///



doc ///
Key
 positionListToArray
 positionArrayToList
 degreeArray
 (degreeArray,List,List)
 (positionListToArray, List, List)
 (positionArrayToList,List)
 [positionListToArray,Verbose]
Headline
 Present the positions of the unfolding parameter used by each equation
Usage
  positionArray=positionListToArray(L,positionList)
  positionList=positionArrayToList(positionArray)
  degArray=degreeArray(L,positionArray)
Inputs
 L: List
  generators of a semigroup ring
 positionList:List
  the positions of the unfolding variables
 positionArray:List
  list of lists of the degrees of the used unfolding parameters for each equation
Outputs
 positionArray:List
  list of lists of positions of the used unfolding parameters for each equation
 positionList:List
  flattened version of the positionArray
Description
  Text
   The function positionArray present the positions sorted by equations; positionArrayToList
   is the inverse function.
  Example
   L={5,7,8,11}
   testWeierstrass(L,4,Verbose=>true)
   degrees source gens semigroupIdeal L
   positionList={0, 10, 19, 32, 33, 44, 45, 46, 59, 60, 61, 62}
   positionArray=positionListToArray(L,positionList)  
   positionArrayToList(positionArray)==positionList      
   (A,unfolding)=makeUnfolding L;
   netList positionListToArray(L,toList(0..numgens A-1))
   netList degreeArray(L,positionListToArray(L,toList(0..numgens A-1)))
   netList positionArray
   netList(degArray=degreeArray(L,positionArray))
   apply(positionList,i-> (degree (gens A)_i)_0)
References
  
SeeAlso
  makeUnfolding
///

doc ///
Key
 dataForML
 (dataForML,List,List)
Headline
 Present the positions of the unfolding parameter used by each equation
Usage  
  {degAll,degRange,degMinList,sF,B}=dataForML(L,minList)
Inputs
 L: List
  generators of a semigroup ring
 positionList:List
  a minimal position list for L
Outputs
  : List
    a list with 5 entries: 
    degAll, degRange and degMinList are degreeArrays, sF is the syzFormat and 
    B is the BettiTally of the semigroupIdeal of L  
Description
  Text
    We compute some data which Machine Learning might use.
  Example
    L={4, 6, 11, 13};
    minList={1, 7, 19, 22, 31, 48, 51, 71, 76};
    dML=dataForML(L,minList);
  Text
    The first three entries are degreeArrays which indicate the degrees of the
    variables present at the universal unfolding, at the degree restricted unfolding
    and at the final minimal unfolding in each of the (in this case 6) equations.  
  Example
    apply(dML_{0..2},degA->netList degA)
  Text
    We see how the variables shrink.

    The dM_3 is the syzFormat of L and dM_4 the betti table of the semigroup ring
    which an ML machine might look at as a string.
  Example
    sF=dML_3
    toString dML_4
    tally values dML_4
  Text
    The total betti number can be obtain from sF or from dML_4 and of course they coincide.
  Example
    sum values dML_4 == sum sF
    sort apply(keys dML_4,k->(k_0,k_2))
  Text
    The last list contains the homological and internat degrees which occure in the minimal
    free resolution of the semigroup ideal.
    
    For human mathematicians the output of displayMinimalFamilies
    is probalby the most enlightening:
  Example
    displayMinimalFamilies{(L,minList)}
  Text
    In this example
    the minimal restricted unfolding has 9 variables. The flattening relations allow to
    prune the base and the family to depend only on three variables with one remaining
    relation: a conic. The last entries shows the in this case 6 equations of the
    final family.
References
  
SeeAlso
  makeUnfolding
  degreeArray
  syzFormat
  BettiTally
  displayMinimalFamilies
  pruneFamily
  
///

doc ///
Key
 verifyOneParameterFamilies
 (verifyOneParameterFamilies,List)
 [verifyOneParameterFamilies,UseMaxMinors]
 [verifyOneParameterFamilies,WithFastMinors]
 [verifyOneParameterFamilies,Verbose]
Headline
 Verify that each one paarmter family is a smoothing of L
Usage  
  LLdone = verifyOneParameterFamilies LLI
Inputs
 LLI: List
  list of pairs (R,L') with R the coordinate ring of a one paramter family
  and  L' the degrees of the variables
Outputs
  LLdone: List
    a list of pairs (L,b) with  L a semigroup and b a Boolean value
Description
  Text
    We check that R is a smoothing defines over QQ of the semigroup ring of L.
    If b==true then L is a Weierstrass semigroup by Pinkham's Theorem.
  Example
    LLI={(QQ[x_0, x_3..x_4, x_2, z]/(x_0^3-x_3^2-z^18,x_4^2-x_0*x_2,x_0*x_3^2-x_4*x_2-x_0*z^18,x_3^2*x_4-x_2^2-x
      _4*z^18,x_3^4-x_0^2*x_4*x_2-z^36),{{6}, {9}, {10}, {14}, {1}}), (QQ[x_0, x_2, x_4..x_5, x_3,
      z]/(x_2^2-x_0*x_4,x_0^3-x_2*x_5,x_0^2*x_2-x_4*x_5,x_5^2-x_0*x_3,x_0^2*x_5-x_2*x_3,x_0*x_2*x_5-x_4*x_3,x_
      0*x_4^2-x_5*x_3-x_0*z^22,x_2*x_4^2-x_0^2*x_3-x_2*z^22,x_4^3-x_0*x_2*x_3-x_4*z^22,x_4^2*x_5-x_3^2-x_5*z^
      22),{{7}, {9}, {11}, {12}, {17}, {1}}), (QQ[x_0..x_3, x_7,
      z]/(x_1^2-x_0*x_2,x_1*x_2-x_0*x_3,x_2^2-x_1*x_3,x_0^3-x_1*x_7,x_0^2*x_1-x_2*x_7,x_0^2*x_2-x_3*x_7,x_0*x_
      3^2-x_7^2-x_0*z^22,x_1*x_3^2-x_0^2*x_7-x_1*z^22,x_2*x_3^2-x_0*x_1*x_7-x_2*z^22,x_3^3-x_0*x_2*x_7-x_3*z^
      22),{{8}, {9}, {10}, {11}, {15}, {1}})};
   LLdone=verifyOneParameterFamilies LLI
   LLdone=verifyOneParameterFamilies(LLI,WithFastMinors=>true)
References
  Pinkham
SeeAlso

///




doc ///
Key
 buchweitz
Headline
 An example of a semigroup that is not a Weierstrass semigroup
Usage
 L = buchweitz i
Inputs
 i:ZZ
Outputs
 L:List
  generators of a semigroup
Description
  Text
   For i>=0 this produces a semigroup B with semigroupGenus 16+i, conductor 26+2i, and
   #sums(2, gaps buchweitz i) = 3*(semigroupGenus B -1)+1). This implies
   that these semigroups are NOT Weierstrass semigroups by the
   following argument, first employed by Buchweitz:

   If L generates the Weierstrass semigroup of a point x
   on a Riemann surface C, then the gaps L is the
   set {1+v | v is the order at p of vanishing of a global
   section of \omega_C}. Thus
   sums(d, #gaps L) <= dim H^0(\omega_C^{d) = d*(2g-1) - g + 1.
  Example
   B = buchweitz 0
   g = #gaps B
   m = 3
   2*(2*g-2) - g + 1
   #sums(2, gaps B)
  Text
Acknowledgement
 The result was written in Ragnar Buchweitz' These d'Etat,
 but never otherwise published by Buchweitz. In the meantime it became
 famous anyway.
///

doc ///
Key
 familyWithSection
 (familyWithSection,List)
 [familyWithSection,Verbose]
Headline
 detect whether the universal family of L has a section
Usage
  ans=familyWithSection L
Inputs
 L:List
   semigroup 
Outputs
 ans:Boolean
  true if the universal family has a section
Description
  Text
   In certain cases the degrees in the minimal fee resolution of the semigroup ideal
   force that the universal family has a (possibly multivalued) section.
   In that case it is plausible that the every fiber is singular at the section.
   The example below is the semigroup of smallest multiplicity and one of two of smallest genus
   where this is true.
  Example
   L={6,9,13,16}
   semigroupGenus L == 13
   familyWithSection L
  Text
   To detect the section we look at the degrees of the
   entries of the lowest degree last syzygy module of the semigroup ideal of L.
  Example
   I = semigroupIdeal L
   semigroupGenus L == 13
   R =ring I;
   fI=res I
   c=length fI
   fI.dd_c_{0}, flatten (degrees fI_3)_{0}
   min flatten (degrees fI.dd_c_{0}^{#L.. rank (fI_(c-1))-1})_0 > (flatten (degrees fI_3)_{0})_0
  Text
   Since min(48,51,55,58) > 47 in this case 4 entries in the universal family
   remain zero for degree reasons and the first #L entries of the corresponding column
   define a section.

   The smallest genus of semigroup with a 2-valued section is 20.
  Example
   L={6,15,19,22}
   I = semigroupIdeal L
   semigroupGenus L == 20
   R =ring I;
   fI=res I
   c=length fI
   fI.dd_c_{0}, flatten (degrees fI_3)_{0}
  Text
   An examples of a semigroups with with five generators and forced section is   
  Example
   L=2*{6,9,13,16}|{6+9}-- a semigroup with 5 generators whose family has a section
   familyWithSection L
   I=semigroupIdeal L; R = ring I
   fI= res I
   fI.dd_4_{0}, degrees (fI_4)
   #gaps L ==33
SeeAlso
  verifyNotWeierstrass
  LabBookProtocol

///
  
///
LLnW={{6, 9, 13, 16}, {8, 9, 12, 13}, {6, 9, 14, 17}, {8, 10, 13, 15}, {6, 9, 16, 19}, {8, 11,
      12, 15}, {6, 9, 17, 20}, {9, 10, 14, 15}, {6, 9, 19, 22}, {8, 12, 13, 17}, {6, 9, 20, 23},
      {6, 15, 19, 22}}

apply(LLnW,L->(fI= res semigroupIdeal L;(L,fI.dd_3_{0}, #gaps L, familyWithSection L)))
///

doc ///
Key
 testSubcomplex
 (testSubcomplex,List)
 (testSubcomplex,ZZ,ZZ,ZZ,ZZ)
 (testSubcomplex,List,List,List,List)
Headline
 check whether a semigroup L with four generators has a subcomplex of format {1,4,4,1}
Usage
  answer=testSubcomplex L
  answer=testSubcomplex(a,b,c,d)
  LL=testSubcomplex(A,B,C,D)
Inputs
 L:List
   a semigroup with four generators
 a:ZZ
 b:ZZ
 c:ZZ
 d:ZZ
   positive integers specifying the semigroup L= {a,a+b,a+b+c,a+b+c+d}
 A:List
 B:List
 C:List
 D:List
   lists of values for (a,b,c,d) which will be tested.
Outputs
 anwers:Boolean
     true if L has format {1,6,8,3} with a subcomplex of format {1,4,4,1}
 LL:List
    of L's for which testSubcomplex L is true
Description
  Text
   For a semigroup with syzformat {1,6,8,3} we test whether the elements of smallet degree
   in the resolution form a subcomplex of format {1,4,4,1}
  Example
   L={6,7,9,10};
   testSubcomplex L
   A=toList(6..11);
   B=toList(1..3);
   C=toList(1..5);
   D=toList(1..3);
   #A*#B*#C*#D
   LL=testSubcomplex(A,B,C,D);
   #LL
   tally apply(LL,L->(fI=res semigroupIdeal L;
	   J= ideal fI.dd_1_{0..3};fJ=res J;
	   apply(4,i->rank fJ_i)=={1,4,4,1}))
  Text
   So the subcomplex is exact in all cases. 
  Example
   LLnW=apply(testNW(A,B,C,D),L->L_0);
   #LLnW
   LLc=select(LL,L->not member(L,LLnW));
   #LLc
  Text
   There are semigroups L with a subcomplex {1,4,4,1} which are Weierstrass.
  Example
   tally apply(LLc,L->(min L,((degreeMatrices L)_2)_(4,0)))
   L={6,9,11,14};
   #gaps L
   (degreeMatrices L)_{1,2}
  Text
   The degree entry 1 in the 8x3 matrix explains why the optimal lower bound for this example is
   zero, and why it is computationally difficult to prove that L={6,9,11,14} is Weierstrass.

   Note that all 4x4 matrices of semigroups in LL have the zero pattern which 
   exhibits two Hilbert-Burch matrices.
  Example
   apply(LLc,L->(fI=res semigroupIdeal L; fI.dd_2_{0..3}^{0..3}))
References
   Eisenbud, Schreyer: Non Weierstrass Examples
SeeAlso
   testNW
   syzFormat
   optimalBound
  

///

/// -* gradings of J *-
 A=toList(6..15);
   B=toList(1..5);
   C=toList(1..10);
   D=toList(1..5);
   #A*#B*#C*#D
elapsedTime LL=testSubcomplex(A,B,C,D); -- 24.3752s elapsed
#LL
tally apply(LL,L->(degreeMatrices L)_2_(4,0))

elapsedTime tally apply(LL,L->(
I=semigroupIdeal L;
R=ring I;
fI=res I;
m4x4=fI.dd_2_{0..3}^{0..3};
<<"semigroup = "<<L<<", m4x4 = "<<m4x4<<flush<<endl;
m4x2=syz (m2x4=(fI.dd_2^{4,5}_{4..7}));
assert(m2x4*m4x2==0);
J=ideal fI.dd_1_{0..3};
sA=syz (A= matrix apply(4,i->(ds=apply(terms (fI.dd_1_(0,i)),m-> (a=(exponents m)_0));ds_0-ds_1)));
B=transpose matrix {L};
assert(A *B==0);
LsA=LLL sA;
betti LsA))

kk=ZZ/nextPrime 10^4;
S=kk[y_1..y_4]


elapsedTime T=tally apply(LL,L->(
I=semigroupIdeal L;
R=ring I;
fI=res I;
m4x4=fI.dd_2_{0..3}^{0..3};
m4x2=syz (m2x4=(fI.dd_2^{4,5}_{4..7}));
assert(m2x4*m4x2==0);
J=ideal fI.dd_1_{0..3};
sA=syz (A= matrix apply(4,i->(ds=apply(terms (fI.dd_1_(0,i)),m-> (a=(exponents m)_0));ds_0-ds_1)));
B=transpose matrix {L};
assert(A *B==0);
LsA=LLL sA;
vectors=LsA*diagonalMatrix apply(2,i->if #select(entries LsA_i,j->j>0)<2 then -1 else 1);
posVect=vectors_(select(2,i->#select(entries(vectors_i),j->j>=0) >=4));
posVect=if rank source posVect==1 then (posVect|posVect+(vectors_{0}+vectors_{1})) else posVect;
assert( #select(2,i->#select(entries(posVect_i),j->j>=0) >=4)==2);
S2=kk[z_0,z_1];
h=apply(entries posVect,d->z_0^(d_0)*z_1^(d_1));
phi=map(S2,S,h);
Jy=ideal mingens ker phi; 
(numgens Jy,rank sub(syz gens Jy,matrix{{0,0,0,0_S}}),posVect)
))
netList keys T

elapsedTime T=tally apply(LL,L->(
I=semigroupIdeal L;
R=ring I;
fI=res I;
m4x4=fI.dd_2_{0..3}^{0..3};
<<"semigroup = "<<L<<", m4x4 = "<<m4x4<<flush<<endl;
m4x2=syz (m2x4=(fI.dd_2^{4,5}_{4..7}));
assert(m2x4*m4x2==0);
J=ideal fI.dd_1_{0..3};
sA=syz (A= matrix apply(4,i->(ds=apply(terms (fI.dd_1_(0,i)),m-> (a=(exponents m)_0));ds_0-ds_1)));
B=transpose matrix {L};
assert(A *B==0);
LsA=LLL sA;
vectors=LsA*diagonalMatrix apply(2,i->if #select(entries LsA_i,j->j>0)<2 then -1 else 1);
kk=coefficientRing R;
S=kk[y_1..y_4,Degrees=>entries vectors];
Jy=ideal sub(gens J,vars S);
assert (isHomogeneous Jy);
Jy
))
#keys T,#LL
L={6,9,13,16}
fI=res semigroupIdeal L
fI.dd_2,fI.dd_3
///

doc ///
Key
 testNW
 (testNW,List)
 (testNW,List,List,List)
 (testNW,ZZ,ZZ,ZZ,ZZ)
 (testNW,List,List,List,List)
 [testNW,WithSectionOnly]
Headline
 check whether a semigroup L with four generators is not a Weierstrass semigroup
Usage
  (L,answer)=testNW L
  (L,answer)=testNW(a,b,c,d)
  LL=testNW(A,B,C,D)
Inputs
 L:List
   a semigroup with four generators and format {1,6,8,3}
 a:ZZ
 b:ZZ
 c:ZZ
 d:ZZ
   positive integers specifying the semigroup L= {a,a+b,a+b+c,a+b+c+d}
 A:List
 B:List
 C:List
 D:List
   lists of values for (a,b,c,d) which will be tested.
Outputs
 anwers:Boolean
  true if L is not a Weierstrass semigroup
  LL: List
    of non Weierstrass semigroups
Description
  Text
   In our paper [ES,xxx] we gave a criterion, which if satisfied shows that a semigroup
   is not Weierstrass. The function returns true, if the criterion is satisfied.
   With the option WithSectionOnly=>true, we only check whether the universal family has a section.
  Example
   L={6,9,13,16}
   semigroupGenus L == 13
   testNW L
  Text
   The smallest example where we have a section but our criterion does not apply has genus 28.
  Example
   L={9, 17, 21, 22}
   semigroupGenus L == 28
   testNW L
   testNW(L,WithSectionOnly=>true)
  Text
   In the second version we check the semigroup generated L= {a,a+b,a+b+c,a+b+c+d}
  Example
   testNW(6,3,4,3)
   elapsedTime LL6=apply(select(apply(toList(1..50),c->testNW(6,3,c,3)),D->D_1),D->D_0);
   gs= apply(LL6,L->semigroupGenus L)
   tally apply(gs,g->g%3)
   missingGenera=select(toList(min gs..max gs),g->not member(g,gs))
  Text
   This suggest that there exists non Weierstrass semigroups of multiplicity 6 for any
   genus g > 12 which is not congruent 0 mod 3.
  Example
   A=toList(6..10);
   B=toList(1..4);
   C=toList(1..7);
   D=toList(1..4);
   elapsedTime LL=testNW(A,B,C,D)
   #LL/(4^2*5*7)+0.0 -- in this range approximately 3 %  of the cases lead to non Weierstrass 
   LLh = sort(addDataToListOfLnW(apply(LL,D->D_0),3),Lh->Lh_2);
   netList apply(LLh,Lh->Lh_{1,2,3})
References
   Eisenbud, Schreyer: Non Weierstrass Examples

SeeAlso
  numericalProofOfNonWeierstrass
  LabBookProtocol
///



doc ///
Key
 testNWfWithAllDegreeConditions
 (testNWfWithAllDegreeConditions,List)
 [testNWfWithAllDegreeConditions,AllDegreeConditions]
Headline
  check whether a semigroup L with four generators is not a Weierstrass semigroup
Usage
  (L,answer)=testNWfWithAllDegreeConditions L
Inputs
 L:List
   a semigroup with four generators and format {1,6,8,3}
Outputs
 anwers:Boolean
  true if L is not a Weierstrass semigroup
Description
  Text
   In our paper [ES,xxx] we gave a criterion, which if satisfied shows that a semigroup
   is not Weierstrass. The function returns true, if the criterion is satisfied.
   With the option WithSectionOnly=>true, we only check whether the universal family has a section.
   The default is WithSectionOnly => false.
  Example
   L={6,9,13,16}
   semigroupGenus L == 13
   testNWfWithAllDegreeConditions L
  Text
   In the file "LLh45-15-30-15s" we listed 3460 semigroups of format 1683 which we believe
   are not Weierstrass enhanced with some further data. These 3460 semigroups are the semigroups which pass
   the first two degree conditions of the 30^2*15^2=202500 examples in
   the range 6..45,1..15,1..30,1..15 for a,b,c,d.
   The following five semigroups are among them.
  Example
   LL={{8, 9, 12, 13}, {6, 15, 22, 25}, {12, 21, 49, 55}, {28, 43, 57, 63}, {45, 58, 74, 87}};
   apply(LL,L->semigroupGenus L)
   elapsedTime tally apply(LL,L->(testNWfWithAllDegreeConditions L)_1)
   apply(LL,L->(I=semigroupIdeal L;fI=res I;fI.dd_3_{0}))
  Text
   The last list gives the crucial column of the third syzygy
   matrix of semigroupIdeal of L. Hence the multi-sections have
   degree 1,2,6,8 or 1 respectively.
   
References
   Eisenbud, Schreyer: Non Weierstrass Examples
SeeAlso
   numericalProofOfNonWeierstrass
   testNW
   LabBookProtocol
   addData
///


/// -* check conjecture in [ES, Non Weierstrass Examples] in 3460 cases*-

LLh=value get "LLh45-15-30-15s";
#LLh==3460
elapsedTime tally apply(LLh,Lh->(L=Lh_0;(testNWfWithAllDegreeConditions L)_1))
-- 281.05s elapsed
--o28 = Tally{true => 3460}
tally apply(LLh,Lh->Lh_7)
-* the degrees of the multi sections
o6 = Tally{1 => 1455}
           2 => 1105
           3 => 174
           4 => 449
           6 => 229
           8 => 34
           9 => 11
           12 => 3
*-
max apply(LLh,Lh -> Lh_1)==617
posm=position(LLh,Lh->Lh_1==617)
netList apply(LLh_{100,20,492,2299,3455},Lh-> Lh_{0,1,7,8,10})
pos=position(LLh,Lh->Lh_7==8)
apply(LLh_{100,20,492,2299,3455},Lh-> Lh_0)

///

///
LLother={({9, 17, 21, 22},true), ({11, 17, 20, 25},true), ({11, 19, 23, 26},true), ({11, 21, 26, 27},true),
      ({12, 22, 27, 29},true), ({14, 24, 29, 33},true), ({15, 19, 21, 22},true), ({15, 19, 28, 36},true),
      ({15, 23, 27, 29},true), ({15, 23, 27, 34},true), ({17, 27, 32, 39},true), ({18, 28, 33, 41},true),
      ({19, 22, 27, 31},true), ({19, 29, 33, 40},true), ({21, 27, 34, 37},true), ({21, 30, 38, 44},true),
      ({22, 25, 34, 40},true), ({22, 25, 35, 39},true), ({24, 32, 38, 39},true)}
sort apply(LLother,D-> (semigroupGenus D_0,D_0))
LLoth=apply(select(LLother,D->not numericalProofOfNonWeierstrass D_0),D->D_0)
LLothh=addDataToListOfLnW(LLoth, 10);
first sort(LLothh,Lh->Lh_1)
))
///

doc ///
Key
 addData 
 (addData,List,ZZ)
 (addDataToListOfLnW,List,ZZ)
Headline
 add data to non Weierstrass semigroups of format {1,6,8,3}
Usage
  Lh=addData(L,n)
  LLh=addDataToListOfLnW(LL,n)
Inputs
 L:List
   a semigroup with four generators and format {1,6,8,3}
 n: ZZ
   an integer specifying how many extra data will be added.
   For values n<7 the function is faster.
Outputs
 Lh:Sequence
   a sequence of upto 9 additional numerical data.
 LLh: List
   a list of sequences of semigroups L with additional data.
Description
  Text
   In our paper [ES,xxx] we gave a criterion, which if satisfied shows that a semigroup
   is not Weierstrass. Which genus occur for which semigroups and how often is not so clear.
   We add data to L in the following order:

   Lh_1 is the genus g of the semigroup L,

   Lh_2 the multiplicity m.

   Lh_3 are the differences between the four generators.
   (We use this together with multiplicity to enumerate L's)

   LH_9 is the gap sequence G of L
   
   Lh_4 give the differences (2k-1)(g-1)-#kG for k=2,3,4,5
   used in the Buchweitz test. They have to be nonnegative for Weierstrass
   semigroups. Our L seem to pass this test always.

   Lh_5 and LH_6 are the weight and the effective weight of L

   Lh_7 is the degree of the multivalued section.

   Lh_8 is a tuple consisting of the list of degrees of generators of the semigroup
   ideal, the degrees of the two relevant generators of fI_2 and fI_3. For a section
   the relevant degree of fI_2 has to be smaller then the relevant degree of fI_3.

   Lh_10 contains the degree of the entries of the crucial 6x4 submatrix of the 6x8
   syzygy matrix.   
  Example
   L={6,9,13,16}
   testNW L
   addData(L,4)
   addData(L,10)
  Text
   The smallest example where we have a section but our criterion does not apply has genus 36.
  Example
   L={15, 19, 21, 22}
   semigroupGenus L == 36
   testNW L
   testNW(L,WithSectionOnly=>true)
   fI=res semigroupIdeal L;
   fI.dd_3_{0}, (degrees fI_3)_0
   Lh=addData(L,10);
   Lh_10, fI.dd_2
  Text
   In case of a list LL of semigroups of the desired form we add data to all L in the list LL
  Example
   LL=apply(select(apply(toList(1..50),c->testNW(6,3,c,3)),D->D_1),D->D_0);
   #LL
   elapsedTime LLh = addDataToListOfLnW(LL,6);
   last LLh
   elapsedTime LLh = addDataToListOfLnW(LL,10);   
   netList apply(LLh_{0..2},D->D_10)

   gs=apply(LLh, D->D_1)
   tally apply(gs,g->g%3)
   missingGenera=select(toList(min gs..max gs),g->not member(g,gs))
  Text
   This suggest that there exists non Weierstrass semigroups of multiplicity 6 for any
   genus g > 12 which is not congruent 0 mod 3.
References
   Eisenbud, Schreyer: Non Weierstrass Examples

SeeAlso
  testNW
  numericalProofOfNonWeierstrass
///

///
needsPackage"AIWeierstrass"
L={15, 34, 121, 197}
#gaps L
I=semigroupIdeal L
R=ring I
fI=res I
fI.dd_3_{0}, degrees fI_3
fI.dd_2
decompose minors(3, fI.dd_2_{0..3})
I_0

(A,unfolding)=makeUnfolding I;
numgens A == 540
min degrees A, max degrees A
range={4,8,12,16}
elapsedTime testWeierstrassRange(L,range,Verbose=>true)==0

///

doc ///
Key
 numericalProofOfNonWeierstrass
 (numericalProofOfNonWeierstrass,List)
Headline
 apply the numerical criterion for non Weierstrass for semigroups of format {1,6,8,3}
Usage
  answer=numericalProofOfNonWeierstrass L
Inputs
 L:List
   a semigroup with four generators and format {1,6,8,3}
Outputs
 answer:Boolean
    true, if L is a non Weierstrass semigroup by our criterion.
Description
  Text
   In our paper [ES,xxx] we gave a criterion, which if satisfied shows that
   a semigroup of syzFormat {1,6,8,3}
   is not Weierstrass. It depends only on the degrees in the minimal
   free resolution of semigroupIdeal of L
  Example
   L={6,9,13,16}
   numericalProofOfNonWeierstrass L
  Text
   The smallest example where we have a section but our criterion does not apply has genus 36.
  Example
   L={15, 19, 21, 22}
   semigroupGenus L == 36
   numericalProofOfNonWeierstrass L
   testNW(L,WithSectionOnly=>true)
References
   Eisenbud, Schreyer: Non Weierstrass Examples
SeeAlso
  testNW
///

///
-- a list of examples with sections which do not pass our testNW
LLwithSection={{15, 19, 21, 22}, {15, 23, 27, 29}, {19, 22, 27, 31}, {19, 29, 33, 40}, {21, 27, 34, 37},
      {21, 30, 38, 44}, {22, 25, 35, 39}, {24, 32, 38, 39}}
tally apply(LLwithSection,L->(testNW(L,WithSectionOnly=>true))_1)
tally apply(LLwithSection,L->(testNW(L))_1)

LLwSh=addDataToListOfLnW (LLwithSection,10);
netList apply(LLwSh,Lh->Lh_{0,1,10})
///




doc ///
Key
 LabBookProtocol
 (LabBookProtocol,List)
 [LabBookProtocol,BaseField]
 [LabBookProtocol,Verbose]
 [LabBookProtocol,ProbTest]
Headline
  print commands which we did to verify computationally that certain semigroup is not Weierstrass
Usage
  answer=LabBookProtocol(L)
Inputs
 L:List
   a semigroup with four generators and format {1,6,8,3}
Outputs
 anwers:Boolean
  true if L is not a Weierstrass semigroup
Description
  Text
   We have verify computationally for a few semigroups with section that it not Weierstrass.
   The computations take too long to be part of an example computation. Instead we
   print the commands we have done together with some timing expectation.
   Running these commands again, does the verification.   
  Example
   LabBookProtocol{6, 9, 13, 16}
   LabBookProtocol{8, 10, 13, 15}
   LabBookProtocol{8, 9, 12, 13}
   LabBookProtocol{6, 15, 19, 22}
   LabBookProtocol{6, 9, 11, 14}
  Text
   These computaions are superflous now, because the theoretical argument of [ES,xxx]
   proves that they are not Weierstrass.
References
   Eisenbud, Schreyer: Non Weierstrass Examples

SeeAlso
  testNW
  verifyNotWeierstrass
  numericalProofOfNonWeierstrass
  LabBookProtocol
///

doc ///
Key
 verifyNotWeierstrass
 (verifyNotWeierstrass,List)
 [verifyNotWeierstrass,BaseField]
 [verifyNotWeierstrass,Verbose]
 [verifyNotWeierstrass,ProbTest]
 [verifyNotWeierstrass,Bound]
 [verifyNotWeierstrass,Factor]
Headline
  verify computationally that a semigroup is not Weierstrass
Usage
  answer=verifyNotWeierstrass(L)
Inputs
 L:List
   a semigroup with four generators and format {1,6,8,3}
Outputs
 anwers:Boolean
  true if L is not a Weierstrass semigroup
Description
  Text
   We can verify computationally for a few semigroups with sections that they are not Weierstrass.
   There are two versions. With ProbTest=>true, we  verify  for a random
   point in the base, that the fiber is singular at the section. If ProbTest=>false then
   we verify this in characteristic zero, provided the base is actually an affine space.
   The main elapsed time is to compute the unversal family over the given finite
   prime field. If the coefficients of the equations of the family are small compared to the size
   of the finite prime, and if the same is true for the coefficients
   in the free resolution of the ideal of the family then we may lift them to ZZ
   and can check that they we still
   have a complex. Frequently, there actually small fractions in the equations and the syzygy matrices.
   In that case we multiply by f=o.Factor and obtain flatness over ZZ[1/f]. The computation that the
   family is singular along the section is then easy. We simply verify that 4 of the equations vanish
   quadratically long the sections. Then all 3x3 minors of the 4x6 relative jaobian matrix
   vanish at the section. The computation takes too long to do an example here. Running the
   following command
 Example
   "elapsedTime verifyNotWeierstrass({6, 9, 13, 16},ProbTest=>false,BaseField=>ZZ/nextPrime 10^6,Factor=>2^5,Bound=>1100)";
 Text
   would proof that L={6,9,13,16} is not a not Weierstrass semigroup for all fields
   of characteristic different from 2.
   
   These computaions are superflous now, because the theoretical argument of [ES,xxx]
   proves that they are not Weierstrass.
References
   Eisenbud, Schreyer: Non Weierstrass Examples

SeeAlso
  testNW
  numericalProofOfNonWeierstrass
  LabBookProtocol
///

-*
doc ///
Key
 pruneFamily
 (pruneFamily, List)
Headline
 Remove removable variables form the base and the family
Usage
 (J1,family1)=pruneFamily(I,J,family);
Inputs
 I: Ideal
   of a semigroup ring
 J: Ideal
   ideal of flattening relations of the family
 family: Matrix
    equations of the family
Outputs
 J1:Ideal
  of the flattening relations of the pruned fanily
 family1: Matrix
   equations of the pruned family
Description
  Text
   The flattening relations frequently allows to remove some of the parameters.
   The function does this.
  Example
   L={6, 9, 10, 11, 13}
   semigroupGenus L
   I=semigroupIdeal(L,BaseField=>ZZ/nextPrime 10^4);
   (A,unfolding)=makeUnfolding I;
   b = semigroupGenus L-3; 
   as=apply(numgens I,i->a=drop(support unfolding_{i},#L));
   rL=apply(#as,i->select(as_i,m->(degree m)_0> b));
   restrictionList=apply(flatten rL,m->sub(m,A));
   (J,family)=getFlatFamily(I,A,unfolding,restrictionList);
   (J1,family1)=pruneFamily(I,J,family);
   J1
   support family1
   support family
   transpose family1
References
  
SeeAlso
  flatteningRelations
  makeUnfolding
///
*-
doc ///
Node
  Key
   pseudoFrobenius
   (pseudoFrobenius, List)
  Headline
   pseudoFrobenius numbers 
  Usage
   psL = pseudoFrobenius L
  Inputs
   L:List
    generators of a semigroup S
  Outputs
   psL:List
    list of pseudoFrobenius numbers of S
  Description
    Text
     computes the pseudoFrobenius numbers of the
     semigroup generated by L (these are the gaps h
     such that s+h is in the semigroup for all s in the
     semigroup; The canonical module is generated by
     {t^(-h) | h is a pseudoFrobenius number.
    Example
     pseudoFrobenius {3,4}
     netList for g from 13 to 20 list (
	 if g%3=!=0 then {g,pseudoFrobenius {6,9,g,g+3}}
	            else continue)
  Caveat
   current method computes a res of the semigroupIdeal.
   probably faster to do by arithmetic.
///

doc ///
Node
  Key
   degreeMatrices
   (degreeMatrices, Complex)
   (degreeMatrices, Ideal)
   (degreeMatrices, List)
  Headline
   degree matrices of the maps in a complex
  Usage
   degmats = degreeMatrices F
   degmats = degreeMatrices I   
   degmats = degreeMatrices L
  Inputs
   F:Complex
   I:Ideal
   L:List
  Outputs
   degmats:List
  Description
    Text
     prints the degree matrices of a complex
    Example
     L = {3,4,5}
     I = semigroupIdeal L
     F = res I
     degreeMatrices F
     degreeMatrices I
     degreeMatrices L
  SeeAlso
   semigroupIdeal
///
   
-* Test section *-

TEST ///-* 0 buchweitzSemigroups*-
debug needsPackage "AIWeierstrass"
assert(buchweitzSemigroups 6 == {})
--elapsedTime buchweitzSemigroups(13,16)
///


     TEST /// -* 1 [check restrictedUnfolding with positionList works] *-
     L={5,6,7}
     semigroupGenus L
     testWeierstrass(L,5)
     I=ideal semigroupRing(L,BaseField=>ZZ/nextPrime 10^4);
     (A,unfolding)=makeUnfolding I;
     #gens A
     positionList=positions(gens A,m->(degree m)_0>5)
     (A,runfolding)=restrictedUnfolding(I,positionList)
     assert(testWeierstrass(I,A,runfolding) == -1)
     ///

     TEST /// -* 2 [check whether using restrictionList works] *-
     L={6,8,9,10};
     I=ideal semigroupRing L;
     (A,unfolding)=makeUnfolding I;
     netList (as=apply(numgens I,i->a=drop(support unfolding_{i},#L)))
     netList apply(numgens I,i->apply(as_i, m->(degree m)_0))--, netList degrees fI_1
     bound=5
     netList (rL=apply(#as,i->select(as_i,m->(degree m)_0> bound)))
     netList apply(#rL,i->apply(rL_i, m->(degree m)_0))
     restrictionList=apply(flatten rL,m->sub(m,A))
     (J,family)=getFlatFamily(I,A,unfolding,restrictionList);
     (J1,family1)=pruneFamily(I,J,family);
     betti J1
     fib=randomFiber(I,J1,family1)
     assert(checkFlatness(I,fib))
     assert(dim singularLocus fib == -1)
          ///

TEST///-* 3 [test of findPoint] *-
--debug needsPackage "AIWeierstrass"
kk=ZZ/101
R=kk[x_0..x_5]
setRandomSeed 0
c=ideal random(R^1,R^{2:-1,2:-2})
point=findPoint c
assert(sub(c,point)== 0)
///	

TEST///-* 4 [flattening and unfolding] *-
--debug needsPackage "AIWeierstrass"
assert ((L = minimalSemigroupGens {5,6, 8,9, 10,12, 13, 17}) == {5, 6, 8, 9})
I=semigroupIdeal L
(A,unfolding)=makeUnfolding I;
assert(numgens A == 68)
J=flatteningRelations(I,A,unfolding);
numgens J
assert(numgens J == 260)
///


TEST/// -* 5 [def1] *-
assert(def1{2,3}  == {-6, -4})
///


     TEST /// -* 6 [withComponents] *-
     L={6, 8, 10, 11, 13}
     I=ideal semigroupRing(L,BaseField=>ZZ/nextPrime 10^4);
     (A,unfolding)=makeUnfolding I;
     b = semigroupGenus L-3; 
     as=apply(numgens I,i->a=drop(support unfolding_{i},#L));
     rL=apply(#as,i->select(as_i,m->(degree m)_0> b));
     restrictionList=apply(flatten rL,m->sub(m,A));
     (J,family)=getFlatFamily(I,A,unfolding,restrictionList);
     (J2,family2)=pruneFamily(I,J,family);
     cJ=decompose J2
     assert(#cJ == 2)
     apply(cJ, J -> betti J)
     apply(cJ,J->withRandomPoint(I,J,family2))
     assert(withComponents(I,cJ, family2) == -1)
     withComponents(I,cJ, family2)
     ///


     TEST /// -* 7 [optimalBound] *-
     L={4,6,15,17}
     semigroupGenus L
     assert( optimalBound({4,6,11})==11)
     ///

     
     TEST /// -* 8 [optimal bound] *-
     L={4,6,11,13}
     semigroupGenus L
     gaps L
     optBound = max select(reverse toList(6..9),b-> testWeierstrass(L,b)==-1)
     assert(testWeierstrass(L,optBound+1)==0)
     assert(testWeierstrass(L,optBound)==-1) 
     ///
     

     TEST /// -* 9 [testWeierstrass] *-
     L={6, 8, 10, 11, 13}
     g=semigroupGenus L
     assert(
	 testWeierstrass(L,g+4)== 0
	 )
     assert(
	 testWeierstrass(L,g-1) == -1
	 )
     ///


TEST /// -* 10 [Buchweitz example of nonsmoothable semigroup and isGapSequence] *-
debug needsPackage "AIWeierstrass"
G=toList(1..12)|{19,21,24,25}
L=isGapSequence G
G1=gaps L
G1==G
assert(#sums(G1,G1)>3*(#G1-1))
///

TEST /// -* 11 [check restrictedUnfolding with positionList works] *-
debug needsPackage "AIWeierstrass"
L={6, 8, 10, 11, 13}
I=ideal semigroupRing(L,BaseField=>ZZ/nextPrime 10^4);
(A,unfolding)=makeUnfolding I;
gens A/degree
positionList=toList(0..40)
(A,runfolding)=restrictedUnfolding(I,positionList)
assert(testWeierstrass(I,A,runfolding) == -1)
///

TEST /// -* 12 [check whether using restrictionList works] *-
L={6,8,9,10};
I=ideal semigroupRing L;
(A,unfolding)=makeUnfolding I;
netList (as=apply(numgens I,i->a=drop(support unfolding_{i},#L)))
netList apply(numgens I,i->apply(as_i, m->(degree m)_0))--, netList degrees fI_1
bound=5
netList (rL=apply(#as,i->select(as_i,m->(degree m)_0> bound)))
netList apply(#rL,i->apply(rL_i, m->(degree m)_0))
restrictionList=apply(flatten rL,m->sub(m,A))
(J,family)=getFlatFamily(I,A,unfolding,restrictionList);
(J1,family1)=pruneFamily(I,J,family);
fib=randomFiber(I,J1,family1)
assert(dim singularLocus fib == -1)
///

TEST /// -* 13 [withComponents] *-

L={6, 8, 10, 11, 13}
I=ideal semigroupRing(L,BaseField=>ZZ/nextPrime 10^4);
(A,unfolding)=makeUnfolding I;
b = semigroupGenus L-3; 
as=apply(numgens I,i->a=drop(support unfolding_{i},#L));
rL=apply(#as,i->select(as_i,m->(degree m)_0> b));
restrictionList=apply(flatten rL,m->sub(m,A));
(J,family)=getFlatFamily(I,A,unfolding,restrictionList);
(J1,family1)=pruneFamily(I,J,family);
cJ=decompose J1;
assert(#cJ == 2)
assert(
    withComponents(I,cJ, family1,Probably=>false)
    == -1)
///
-* currently fails because of printing in testWeierstrass
TEST /// -* 14 [withRandomPoints] 
L={6, 8, 10, 11, 13}
g=semigroupGenus L
assert(withRandomPoint(L,g+5,Probably=>true)== 0)
assert(withRandomPoint(L,g-3) == -1)
///
*-

TEST /// -* 15 [locally minimal family] *-
L={5,9,13}	 
optBound=optimalBound L 
initialList=prepareInitialPositionList(L)
finalList=systematicShrinking(L,initialList)

(J,family,runfolding,J1)=showRestrictedFamily(L,finalList); 
J, J1
transpose runfolding
transpose family
support family
support runfolding
assert(sub(family,ring runfolding)==runfolding%sub(J1,ring runfolding))
///

TEST/// -* 16 [positionListToArray] *-
L={6,8,10,11}
positionList=prepareInitialPositionList(L)
positionArray=positionListToArray(L,positionList,Verbose=>true)
assert(positionList == positionArrayToList(positionArray))
assert(positionArray==positionListToArray(L,positionList))
///

TEST/// -* 17 [optimalRange and testWeierstrassRange ] *-
L={6, 8, 10, 11, 13}
guess=12
b = optimalBound(L,guess)
assert (testWeierstrass(L,b) ==-1)
assert (testWeierstrass(L,b+1) ==0)
I=semigroupIdeal L
guess = 12
amax = max flatten degrees source gens I
assert(testWeierstrassRange(L, toList(b+2..amax)) == 0)
assert(testWeierstrassRange(L, toList(b+1..amax)) == -1)

range = optimalRange(L,b,Probably=>true)
assert(range == {12,13,14})
///


computeLL4wS=method(Options=>{Verbose=>true})


computeLL4wS(ZZ) := o -> gmax -> (
    LL:=null; LL4:= null; LL1683:=null;LLwS:=null;I:=null; fI:=null;
    LL4wS:=if o.Verbose  then (
	for g from 12 to gmax list (
	<<flush<<endl;
	elapsedTime LL=findSemigroups g;	
	elapsedTime LL4=select(LL,L->#L==4);	
	<<"genus = "<<g<<", #LL = "<<#LL<<" ,#LL4 = " << #LL4 <<flush<<endl;
	elapsedTime LL1683=select(LL4,L->syzFormat L=={1,6,8,3});
	<<"#LL1683 = " << #LL1683 <<flush<<endl;
	elapsedTime LLwS=select(LL1683,L-> (
		I=semigroupIdeal L;fI=res I;
		min (degrees fI_2)_{4..7}>degree fI_3_0));
	<<"#LLwS = " << #LLwS <<flush<<endl;
	LLwS)) else (
	for g from 12 to gmax list (
	--<<flush<<endl;
	LL=findSemigroups g;
	LL4=select(LL,L->#L==4);	
	--<<"genus = "<<g<<", #LL = "<<#LL<<" ,#LL4 = " << #LL4 <<flush<<endl;
	LL1683=select(LL4,L->syzFormat L=={1,6,8,3});
	--<<"#LL1683 = " << #LL1683 <<flush<<endl;
	LLwS=select(LL1683,L-> (
		I=semigroupIdeal L;fI=res I;
		min (degrees fI_2)_{4..7}>degree fI_3_0));
	--<<"#LLwS = " << #LLwS <<flush<<endl;
	LLwS));
    flatten LL4wS)
/// -*[ LL4wS ] *-
elapsedTime LL4wS=computeLL4wS 15
LLnW={{6, 9, 13, 16}, {8, 9, 12, 13}, {6, 9, 14, 17}, {8, 10, 13, 15}, {6, 9, 16, 19}, {8, 11,
      12, 15}, {6, 9, 17, 20}, {9, 10, 14, 15}, {6, 9, 19, 22}, {8, 12, 13, 17}, {6, 9, 20, 23},
      {6, 15, 19, 22}}
netList apply(LLnW,L->(I=semigroupIdeal L; R = ring I;
          fI= res I;
 (#gaps L, (testNW L)_0,fI.dd_2_{0..3}, fI.dd_3_{0}, matrix (degrees fI_3))))

L={12,13,18,32}
apery {6,9,13,16}
semigroupGenus {6,9,13,16}
-- Torres trick: The semigroup L with
oddGenerator=241 -- or larger
L={12,18,26,32,oddGenerator}
g=#gaps L
--are not Weierstrass because
d=32
r=4
eps=(d-1)%(r-1)
m=sub((d-1-eps)/(r-1),ZZ)
assert (d-1==m*(r-1)+eps)
pi0=sub((r-1)*m*(m-1)/2+m*eps,ZZ)-- castelnouvo's bound an curves in P^r
g>pi0 
-- shows that |32p|: C -> C0 \subset P^4 would factors 2:1 over a curve with
-- Weierstrass semigroup L={6,9,13,16}. However this semigroup is not Weierstrass.
I=semigroupIdeal L; R = ring I
fI= res I
fI.dd_4_{0}, degrees (fI_4) --no direct argument with section seem to work


L={12,18,26,32,6+9} -- a semigroup with 5 generators whose family has a section
I=semigroupIdeal L; R = ring I
fI= res I
fI.dd_4_{0}, degrees (fI_4)
#gaps L ==33



L={12,18,26,32,6+13} -- a semigroup with 5 gens where  a subfamily has a section
I=semigroupIdeal L; R = ring I
fI= res I
fI.dd_4_{0}, degrees (fI_4)
#gaps L==35 

L={12,18,26,32,9+16}
I=semigroupIdeal L; R = ring I
fI= res I
fI.dd_4_{0}, degrees (fI_4)
#gaps L==38

--------------------
-- children of non Weierstrass semigroup {6,9,13,16}
L={9,12,26,32}
testNW L
#gaps L
I=semigroupIdeal L; R = ring I
fI= res I
fI.dd_3_{0}, degrees (fI_3)

L={12,13,18,32}
testNW L
#gaps L
I=semigroupIdeal L; R = ring I
fI= res I
fI.dd_3_{0}, degrees (fI_3)
------------------------- end children
LLnW15=select(LLnW,L-> semigroupGenus L <16)
assert(LLnW15==LL4wS)

tally apply(LLnW,L->(G=gaps L; g=#G; Gi=G;
	apply(5,i->(Gi=sums(Gi,G);(2*i+3)*(g-1)-#Gi))))
tally  apply(LLnW,L->(G=gaps L; g=#G))
///

-* 
numericalProofOfNonWeierstrass=method()
numericalProofOfNonWeierstrass(List) := L -> (
    fL := res semigroupIdeal L;
    m3 := matrix apply(flatten degrees fL_2,d->apply(flatten degrees fL_3,e->e-d));
    m2 := matrix apply(flatten degrees fL_1,d->apply(flatten degrees fL_2,e->e-d));
    m3_(4,0)<0 and m2_(4,2) <min L)
   
    kosMat := syz transpose fL.dd_3_{0}^{0..3};
    dK:=transpose matrix apply(flatten degrees target kosMat,
	d->apply(flatten degrees source kosMat,e->
	    if member(e-d,L) then e-d else -1));
     --m2_{0..3},dK,m3_{0}^{0..3}
     kmins:=apply(4,i->min select(flatten entries dK_{i},d-> d>0));
     i:=null;j:=null;
     (
     m2_(3,0)<kmins_0
     and
    all({0,1,2},i->m2_(4,i)<kmins_i)
    and
    all({0,1,2},i->m2_(5,i)<kmins_i)
    )
)
*-
degreeMatricesOld = method()
degreeMatricesOld(List) := L-> (
    fL := res semigroupIdeal L;
    m1 := matrix apply(flatten degrees fL_0,d->apply(flatten degrees fL_1,e->e-d));
    m2 := matrix apply(flatten degrees fL_1,d->apply(flatten degrees fL_2,e->e-d));
    m3 := matrix apply(flatten degrees fL_2,d->apply(flatten degrees fL_3,e->e-d));
    kosMat := syz transpose fL.dd_3_{0}^{0..3};
    dK:=transpose matrix apply(flatten degrees target kosMat,
	d->apply(flatten degrees source kosMat,e->
	    if member(e-d,L) then e-d else -1));
     (
      transpose m1,m2_{0..3},dK,m3_{0}^{0..3},fL.dd_2
      )
  )



-- degreeMatrices(List) := L-> (
--     fL := res semigroupIdeal L;
--     c:=length fL;
--     ms:=apply(c,i-> matrix apply(flatten degrees fL_i,d->apply(flatten degrees fL_(i+1),e->e-d)));
--     ms)




subFamilyWithSection = method()
subFamilyWithSection List :=  L -> (
    if not gcd L == 1 then return (L,false);
    if not #minimalSemigroupGens L == #L then return (L,false);
    fI := res semigroupIdeal L;
    c:= length fI;
    if not (fI.dd_c_{0})^{#L..rank fI_(c-1)-1} == 0 then return (L,false);
    b:=(degree fI_c_0)_0-(degree fI_(c-1)_(#L))_0;
    (L,true,b)
    )


///
restart
needsPackage "AIWeierstrass"
LLdifficult={{6, 8, 17, 19, 21},--sgrp4
    {6, 8, 10, 19, 21, 23}, --sgrp1
    {6, 9, 11, 14}, --sgrp3
    {8, 9, 11, 15, 21}}--sgrp2
L=LLdifficult_1
apply(LLdifficult,L->subFamilyWithSection L)

g=12
elapsedTime LL=select(findSemigroups g,L->not knownExample L and L_0>5);#LL
LLb=apply(LL,L->subFamilyWithSection L);
elapsedTime LLwBetterBound=select(LLb,c->c_1);
#LLwBetterBound
LLwBetterBound
(L,ans, b)=last LLwBetterBound
I=semigroupIdeal L;R=ring I
fI=res I
fI.dd_3, degrees fI_1
range={10,20,30} 
elapsedTime testWeierstrassRange(L,range)
elapsedTime testWeierstrass(L,9)
LL=reverse sort(LL,L->ewt L)
elapsedTime netList apply (LL,L->(I=semigroupIdeal L;elapsedTime (A,unfolding)=makeUnfolding I;
	(ewt L,weight L, numgens A,L))) -- 180.836s elapsed
LL12done=getFromDisk "bounds12";
#LL12done,#LL


///




///   
restart
needsPackage "AIWeierstrass"
L = {6,8,10,12}
L1 = {6,9,13,16}
numericalProofOfNonWeierstrass L --error
syzFormat L
testNW (L, WithSectionOnly => true)
testNW L1
///

///
restart
needsPackage "AIWeierstrass"
L = {6,9,13,16}
testNW (L, WithSectionOnly => true)
testNW L
n = 20
L = LL_0
LL = makeArithmeticProgression(60, 6, 6)
testNWListOfLists LL

elapsedTime LL=testNW(A,B,C,C)
Lg = apply(LL, L -> semigroupGenus L_0)
dif1 = G -> apply(#G-1, i-> G_(i+1) - G_i)
dif1 apply(#Lg, i -> Lg_i-33)
gFroma = (2,n) -> 2*n^2+16*n+33

for n from 0 to 5 list gFroma n

dif1 dif1 Lg

--(a,b,c,d) = (20,10,10,10)
(a,b,c,d) = (5,2,2,2)
A = toList (6..5+a)
B = toList(1..b)
C = toList (1..c)
D = toList(1..d)
elapsedTime LL=testNW(A,B,C,D);
#LL  -- 308.573s elapsed for 2*10^4


elapsedTime LLs=testNW(A,B,C,D,WithSectionOnly=>true); #LLs
frequencies=tally values (Tg=tally apply(LL,D->#gaps D_0))
min keys Tg,max keys Tg
possibelGenusGaps=select(toList(min keys Tg..max keys Tg),g->not member(g, keys Tg))

elapsedTime LLenhanced=addDataToListOfLnW(LL,6);-- 21.8964s elapsed
addData ((first LL)_0,6)
LLenhanced=sort(LLenhanced,L->L_1);
netList apply(LLenhanced_{0..29},ld->(ld_1,ld_2,ld_3,ld_4))


LL1h=select(LLenhanced,ld->ld_3_0==ld_3_2 and ld_4_3==7);#LL1h
LL1hs=sort(LL1h,ld-> ld_3);
netList apply(LL1hs,ld->(ld_1,ld_2,ld_3))
LL1ha=select(LL1hs,ld->ld_3_0%2==1);
netList apply(LL1ha,ld->(ld_1,ld_2,ld_3))
netList select(LL1ha,ld->ld_2==6)


LL6=apply(select(apply(toList(1..50),c->testNW(6,3,c,3)),D->D_1),D->D_0);
LL6g=apply(LL6,L->#gaps L)
tally apply(LL6g,g->g%3)
--elapsedTime LL6h=addDataToListOfLnW LL6;
tally apply(LL6h,lh->lh_1%3)

LL8=apply(select(apply(toList(1..200),c->testNW(8,4,c,4)),D->D_1),D->D_0);#LL8
LL8g=apply(LL8,L->#gaps L)
tally apply(LL8g,g->g%4)

elapsedTime LL8h=addDataToListOfLnW(LL8,6);
tally apply(LL8h,lh->lh_1%3)

LL10=apply(select(apply(toList(1..200),c->testNW(10,5,c,5)),D->D_1),D->D_0);#LL10
LL10g=apply(LL10,L->#gaps L)
tally apply(LL10g,g->g%4)

elapsedTime LL10h=addDataToListOfLnW(LL10,6);
tally apply(LL10h,lh->lh_1%3)
tally apply(LL10h,lh->lh_1%4)

LL14=apply(select(apply(toList(1..200),c->testNW(14,7,c,7)),D->D_1),D->D_0);#LL14
LL14g=apply(LL14,L->#gaps L)
tally apply (LL14g,g->g%10)

elapsedTime LL14h=addDataToListOfLnW(LL14,6);
tally apply(LL14h,lh->lh_1%6)


LL12=apply(select(apply(toList(1..200),c->testNW(12,6,c,6)),D->D_1),D->D_0);#LL12
LL12g=apply(LL12,L->#gaps L)
tally apply(LL12g,g->g%10)


gs=sort unique (LL6g|LL8g|LL10g|LL12g|LL14g)
gs=select(gs,g->g<150);
#gs
genusGaps=select(toList(min gs..max gs),g->not member(g,gs))
tally apply(genusGaps,g->g%12)
select(gs,g->g%6==3)
apply(#genusGaps-2,i->genusGaps_(i+1)-genusGaps_i)

#LL,#LLs
first LL, first LLs
LLother=select(LL,L-> not member(L,LLs));#LLother
toString LLother
-*
LLother={({9, 17, 21, 22},true), ({11, 17, 20, 25},true), ({11, 19, 23, 26},true), ({11, 21, 26, 27},true),
      ({12, 22, 27, 29},true), ({14, 24, 29, 33},true), ({15, 19, 21, 22},true), ({15, 19, 28, 36},true),
      ({15, 23, 27, 29},true), ({15, 23, 27, 34},true), ({17, 27, 32, 39},true), ({18, 28, 33, 41},true),
      ({19, 22, 27, 31},true), ({19, 29, 33, 40},true), ({21, 27, 34, 37},true), ({21, 30, 38, 44},true),
      ({22, 25, 34, 40},true), ({22, 25, 35, 39},true), ({24, 32, 38, 39},true)}
*-
gs=sort unique (apply(LL,D->#gaps D_0)|gs)

LLenhanced=addDataToListOfLnW LL;
genusGaps=select(toList(min gs..max gs),g->not member(g,gs))
apply(oo,g->g%6)

///

///


restart
needsPackage "AIWeierstrass"
L = {6,9,13,16}
testNW L
(a,b,c,d) = (25,10,20,10)
A = toList (6..a)
B = toList(1..b)
C = toList (1..c)
D = toList(1..d)
elapsedTime LL=testNW(A,B,C,C);#LL
first LL
LL=apply(select(LL,D->D_1),D->D_0);#LL
gms=sort apply(LL,L->(#gaps L,L_0));
Tgm=tally gms;
tally values Tgm
Tg=tally (gs=apply(gms,gm->gm_0));
tally values Tg
genusGaps=select(toList(min gs..150),g->not member(g,gs))
genusGaps=={18, 130, 140}

-*
LLbad={{9, 17, 21, 22}, {11, 17, 20, 25}, {11, 19, 23, 26}, {11, 21, 26, 27}, {12, 22, 27, 29}, {14, 24,
       29, 33}, {15, 19, 21, 22}, {15, 19, 28, 36}, {15, 23, 27, 29}, {17, 27, 32, 39}, {18, 28, 33, 41},
       {19, 22, 27, 31}}

*-

-*
-- for a in 6..20, b in 1..5 c in 1..10, d in 1..10
       -- 13.4399s elapsed

o25 = Tally{{1, 3, 5, 7, 9, 11, 13, 15} => 66    }
            {1, 3, 7, 11, 15, 19, 23, 27} => 8
            {1, 3, 7, 12, 17, 22, 27, 33} => 3
            {1, 4, 8, 12, 16, 20, 24, 29} => 1
            {1, 5, 9, 13, 17, 22, 27, 33} => 4
            {2, 6, 10, 14, 18, 22, 26, 30} => 50
            {4, 12, 20, 28, 36, 44, 52, 60} => 10

 -- 105.481s elapsed

o21 = Tally{{1, 3, 5, 7, 9, 11, 13, 15, 17, 19, 21, 23, 25, 27, 29, 31, 33, 35} => 66          }
            {1, 3, 7, 11, 15, 19, 23, 27, 31, 36, 41, 46, 51, 57, 63, 69, 75, 81} => 3
            {1, 3, 7, 11, 15, 19, 23, 27, 31, 36, 41, 46, 51, 57, 63, 69, 75, 82} => 5
            {1, 3, 7, 12, 17, 22, 27, 33, 39, 45, 51, 57, 63, 69, 75, 81, 87, 93} => 1
            {1, 3, 7, 12, 17, 22, 27, 33, 39, 45, 51, 58, 65, 72, 79, 86, 93, 100} => 1
            {1, 3, 7, 12, 17, 22, 27, 33, 39, 45, 51, 58, 66, 74, 82, 90, 98, 106} => 1
            {1, 4, 8, 12, 16, 20, 24, 29, 34, 39, 45, 51, 57, 63, 69, 75, 81, 87} => 1
            {1, 5, 9, 13, 17, 22, 27, 33, 39, 45, 51, 57, 63, 69, 75, 81, 87, 93} => 2
            {1, 5, 9, 13, 17, 22, 27, 33, 39, 46, 53, 60, 67, 74, 81, 88, 95, 102} => 2
            {2, 6, 10, 14, 18, 22, 26, 30, 34, 38, 42, 46, 50, 54, 58, 62, 66, 70} => 50
     {4, 12, 20, 28, 36, 44, 52, 60, 68, 76, 84, 92, 100, 108, 116, 124, 132, 140} => 10

*-



///



end--

restart
    needsPackage "AIWeierstrass"
     
     installPackage "AIWeierstrass"
     viewHelp "AIWeierstrass"

     check "AIWeierstrass"
--     loadPackage "AIWeierstrass"
     uninstallPackage "AIWeierstrass"
     restart
     installPackage "AIWeierstrass"
     
     viewHelp "AIWeierstrass"
     check "AIWeierstrass"
 --    loadPackage ("AIWeierstrass",Reload=>true)
     -* Development section *-



///
LLnW={{6, 9, 13, 16}, {8, 9, 12, 13}, {6, 9, 14, 17}, {8, 10, 13, 15}, {6, 9, 16, 19}, {8, 11,
      12, 15}, {6, 9, 17, 20}, {9, 10, 14, 15}, {6, 9, 19, 22}, {8, 12, 13, 17}, {6, 9, 20, 23},
      {6, 15, 19, 22}}


	
restart
     needsPackage "AIWeierstrass"  
///

///
L={6, 9, 13, 16};  semigroupGenus L-- 1751.42s elapsed
I=semigroupIdeal L;
kk=coefficientRing ring I
R=kk[(support I)_{1,2,3,0},Degrees=>{9,13,16,6}]
fI=res sub(I,R)
transpose fI.dd_1,fI.dd_2||transpose fI.dd_3_{0}
transpose fI.dd_1_{0..3},fI.dd_2_{0..3}||transpose fI.dd_3_{0}^{0..3}||(transpose syz transpose fI.dd_3_{0}^{0..3})^{5,4,3,2,1,0}
-*
o48 = ({-18} | x_3^2-x_0^3     |, {18}  | -x_1 -x_4  0    0      |)
       {-22} | x_3x_1-x_4x_0   |  {22}  | x_3  x_0^2 -x_4 x_1x_0 |
       {-25} | x_3x_4-x_1x_0^2 |  {25}  | x_0  x_3   x_1  -x_4   |
       {-32} | x_4^2-x_1^2x_0  |  {32}  | 0    0     -x_0 x_3    |
                                  {39}  | 0    0     0    0      |
                                  {42}  | 0    0     0    0      |
                                  {-47} | x_4  -x_1  x_3  x_0    |
                                  {18}  | x_1  x_4   0    0      |
                                  {22}  | -x_3 0     x_4  0      |
                                  {25}  | -x_0 0     0    x_4    |
                                  {25}  | 0    x_3   x_1  0      |
                                  {28}  | 0    x_0   0    x_1    |
                                  {32}  | 0    0     -x_0 x_3    |
*-
L={6, 15, 19, 22};  semigroupGenus L




L={8, 9, 12, 13}; semigroupGenus L -- 473.106s elapsed
L={6, 9, 14, 17};  semigroupGenus L-- 1471.8s elapsed
L={8, 10, 13, 15};  semigroupGenus L -- 144.899s elapsed
L={6, 9, 16, 19};  semigroupGenus L

L={6, 15, 19, 22};  semigroupGenus L
I=semigroupIdeal L;
fI=res I
transpose fI.dd_1_{0..3},fI.dd_2_{0..3}||transpose fI.dd_3_{0}^{0..3}||(transpose syz transpose fI.dd_3_{0}^{0..3})^{5,4,3,2,1,0}
I0=ideal (gens I%x_0)
fI0=res I0
transpose fI0.dd_1_{0..5},fI0.dd_2||transpose fI0.dd_3
m2x4=matrix{{x_0^2,x_3,x_1,x_4},{x_3,x_0^3,x_4,x_1*x_0}}
gens minors(2,m2x4)%I
gens I%minors(2,m2x4)
gens I
J=ideal (gens I)_{0..3}
fJ=res J
codim J, codim I
J2=ideal((gens I)_{0..2})
codim J2, codim J, codim I
residual =J2:J
primaryDecomposition J2
transpose fI.dd_1, fI.dd_2
support I/degree
///

 

tally apply(LLnW,L->semigroupGenus L)
tally apply(LLnW,L->L_1-L_0==L_3-L_2)

netList apply(LLnW,L->(I=semigroupIdeal L; fI=res I;
	(L,semigroupGenus L,fI.dd_3_{0}),(degrees fI_3)_0))

L = LLnW_0
elapsedTime verifyNotWeierstrass L

elapsedTime LL4wS=computeLL4wS 20
LLnW={{6, 9, 13, 16}, {8, 9, 12, 13}, {6, 9, 14, 17}, {8, 10, 13, 15}, {6, 9, 16, 19}, {8, 11,
      12, 15}, {6, 9, 17, 20}, {9, 10, 14, 15}, {6, 9, 19, 22}, {8, 12, 13, 17}, {6, 9, 20, 23},
      {6, 15, 19, 22}}
assert(LLnW==LL4wS)
	
-- could try to construct LL4 faster
goldenRatio=(1+sqrt 5)/2
goldenRatio^2*96/60
flatten	 LL4wS	
	

///


restart
needsPackage "AIWeierstrass"

L={6,9,13,16}
I=semigroupIdeal L
R=ring I
betti (fI=res I)
fI.dd_3_{0}
fI.dd_2_{0..3}
J=ideal(fI.dd_1_{0..3})
primaryDecomposition J
fJ=res J
fI
extend(fI,fJ,id_(R^1))
res ideal fI.dd_1_{0..3,5}
I
m2x3=matrix{{x_1,x_0,x_3},{x_4,x_3,x_0^2}}

m3x2=syz fI.dd_1_{1,4,5}
betti (fJ=res trim(minors(2,m2x3)+minors(2,m3x2)))
M5x5=diagonalMatrix{1,1,1,1,-1}*fJ.dd_2^{4,3,2,1,0}*diagonalMatrix{-1,1,1,1,1}
M5x5+transpose M5x5
N=M5x5^{0,1,3,2,4}_{0,1,3,2,4}
toString N
N=matrix {{0, 0, -x_3, x_0, x_1}, {0, 0, x_0^2, -x_3, -x_4}, {x_3, -x_0^2, 0,
      -x_1^2, -x_0*x_3^3}, {-x_0, x_3, x_1^2, 0, 0}, {-x_1, x_4, x_0*x_3^3, 0, 0}}

J=pfaffians(4,N)



rest=J:I
M5x5
dim J, degree J, dim I,degree I,dim rest, degree rest
intersect(I,rest)==J
trim(I+rest)
J1=intersect(ideal{x_0,x_3,x_4^2},I)
(gens minors(2,m2x3))%I==0
L = {5, 12, 13, 19}
dL = produceData({L},"crash2", "KillFile" => false, Verbose => true)
displayMinimalFamilies dL



LL = {{3, 11, 13}, {3, 10, 14}, {4, 7, 10}, {4, 7, 13}, {4, 6, 11}, {4, 10, 11, 13}, {4, 9, 11, 14}, {4, 6, 13, 15}, {4, 9, 10, 15}, {5, 8, 9, 12}, {5, 8, 9, 11}, {5, 7, 9, 13}, {5, 9, 11, 12, 13}, {5, 7, 9, 11}, {5, 6, 9}, {5,
      7, 8}, {5, 8, 11, 12, 14}, {5, 7, 11, 13}, {5, 6, 13, 14}, {6, 8, 9, 10, 11}, {6, 9, 10, 11, 13, 14}, {6, 8, 10, 11, 13, 15}, {6, 7, 10, 11, 15}, {6, 8, 9, 11, 13}, {6, 7, 9, 11}, {6, 7, 8, 11}, {6, 8, 9, 10, 13}, {6, 7,
      9, 10}, {6, 7, 8, 10}, {6, 7, 8, 9}, {7, 9, 10, 11, 12, 13, 15}, {7, 8, 10, 11, 12, 13}, {7, 8, 9, 11, 12, 13}, {7, 8, 9, 10, 12, 13}, {7, 8, 9, 10, 11, 13}, {7, 8, 9, 10, 11, 12}, {8, 9, 10, 11, 12, 13, 14, 15}}
#LL

dL = produceData(LL_{31..36},"td7", "KillFile" => false)

case = 30, semigroup = {7, 9, 10, 11, 12, 13, 15}
AIWeierstrass.m2:1078:20:(3):[22]: error: recursion limit of 300 exceeded
AIWeierstrass.m2:1078:20:(3): entering debugger (enter 'help' to see commands)
AIWeierstrass.m2:1078:8-1078:44: --source code:
    p = randomPoints(cR1,Homogeneous=>false);

LL = findSemigroups 9;
#LL
LL = select(LL, L -> not knownExample L);
#LL
dL = produceData(LL,"td9", "KillFile" => false)

restart
needsPackage "AIWeierstrass"
L  =  {8, 9, 10, 11, 12, 13, 14, 15}
debug AIWeierstrass
elapsedTime produceData({L}, "crashPoint", Verbose =>true)

cR2 = ideal prune(R1/cR1)
transpose matrix findPoint(cR1)
transpose matrix randomPoints(cR1)
describe ring c
options randomPoints
viewHelp (prune,Ring)

elapsedTime while(p = (randomPoints cR2)_0;
       product p ==0) do ();p


restart
needsPackage "AIWeierstrass"

openFiles()
run"ls -ltr"

LL = select(findSemigroups 9, L-> #L>2)
#LL
dL = produceData(LL,"td9", Verbose => true , "KillFile" => false)

crash case:{6, 9, 10, 11, 13, 14}
g=10

restart
needsPackage "AIWeierstrass"
g=9
LL=select(findSemigroups g, L-> #L >2)
#LL
LL = reverse sort(LL, L-> ewt L)
#LL
LL = drop(LL, -2)
#LL
--LL = reverse sort(LL, L-> weight L)
run "ls -ltr"
name="bounds"|toString g

elapsedTime dLbounds=produceBounds(LL,name, Verbose => false)

LL = reverse sort(LL, L-> wt L)
run "ls -ltr"
--run "rm bounds6"
name="bounds6b"
elapsedTime dLbounds=produceBounds(LL,name, Verbose => false)

apply(#LL, i->(i, LL_i, ewt LL_i))

 
LLdifficult={{6, 8, 17, 19, 21},
    {6, 8, 10, 19, 21, 23},
    {8, 9, 11, 15, 21}}
LLdifficult/ewt

L=last LLdifficult
I=semigroupIdeal L
R=ring I
fI=res I
fI.dd_4, degrees fI_4
fI.dd_2
range={2,4,6,8,10,12,14,16,18,20}
elapsedTime testWeierstrassRange(L,range,Verbose=>true)

elapsedTime apply(LLdifficult,L->elapsedTime testWeierstrass(L,0,Verbose=>true,Probably=>true))
name="difficultBounds11"
elapsedTime dLbounds=produceBounds(LLdifficult,name, Verbose => true)

apply(#LL, i->(i, LL_i, ewt LL_i))

L= LLdifficult_0
testWeierstrass (L, 0, Verbose =>true, Probably =>true)

--------------- g=12 -----
restart
needsPackage "AIWeierstrass"
viewHelp "AIWeierstrass"
g=12
LL=findSemigroups g;#LL
LL=select(LL, L->not knownExample L and min L >5);#LL
LL=reverse sort(LL,L->ewt L);
i=0
elapsedTime LLs=sort(LL,L->(I=semigroupIdeal L;elapsedTime (A,unf)=makeUnfolding I;
	a=numgens A;<<"case = "<<i<<", size of A = "<<a<<flush<<endl;i=i+1; a));
run "ls -ltr"
L=first LLs
I=semigroupIdeal L;(A,unf)=makeUnfolding I;numgens A
nameLL="LL12sorted"
openOutAppend nameLL;
nameLL <<LLs;
nameLL<<close;
run "ls -ltr"
restart
debug needsPackage "AIWeierstrass"
name="bounds12"
LLs=toList value get "LL12sorted";#LLs
tB=getFromDisk name;#tB
last tB
LLs_107
tB'=continueComputation(produceBounds,LLs,name,Verbose=>true)
  


LL = select(findSemigroups 8, L->#L>2)
LL =drop(reverse sort(LL, L->ewt L), -2)
#LL
pdb8 = getFromDisk"bounds8"
#pdb8
(reverse pdb8)_{0..5}/first/ewt
run "ls -ltr"
run "rm pdr8"
produceRangesFromBounds(pdb8, "pdr8")

needsPackage "AIWeierstrass"
LL = select(findSemigroups 9, L->#L>2)
LL =drop(reverse sort(LL, L->ewt L), -2)
#LL
continueComputation(produceBounds,LL,0,"bounds9")

pdb8 = getFromDisk"bounds9" ;#pdb8
produceRangesFromBounds(pdb8, "pdr8")
getFromDisk "pdb8"

needsPackage "AIWeierstrass"
pdb9 = getFromDisk"bounds9" ;#pdb9
produceRangesFromBounds(pdb9, "pdr9") --2:45: up to 55

LL = select(findSemigroups 10, L->#L>2)
LL =drop(reverse sort(LL, L->ewt L), -2)
#LL
produceBounds (LL, "tdb10") --2:45 up to 105

-- try to get upto 10 minLists for each L
td6=flatten getFromDisk "tD6new"
degArrays6=apply(td6,D->(L=D_0;minL=D_1;(L,degreeArray(L,positionListToArray(L,minL)))))
netList apply(degArrays6,ar->(ar_0,netList ar_1))
netList( altranges6=unique apply(degArrays6,ar->(ar_0,sort unique flatten ar_1)))
name="manyMinLists"
elapsedTime many6=produceMinListsFromRanges(altranges6,10,name)
minLists6=unique flatten getFromDisk "manyMinLists"
displayMinimalFamilies minLists6
 #(minLists6a= getFromDisk "manyMinLists")
displayMinimalFamilies (minLists6a)_10

--nearly ordinary Weiertrass points
g=6, t=g+1
L=minimalSemigroupGens (toList(g..t-1)|toList(t+1..2*g+1))
gaps L==toList(1..g-1)|{t}
b=optimalBound(L,g,Verbose=>true,Probably=>true)


semigroupFromGaps = method()
semigroupFromGaps List := List => G -> (
    F := max G;
    G0 := for i from 1 to F list if  not isMember(i, G) then i else continue;
    G1 := toList (F+1..2*F+2);
    minimalSemigroupGens(G0|G1))
smallWeightSemigroups = g -> (
    G0 := toList(1..g-1);
    GG := apply(g-1,i-> G0|{g+i});
    apply(GG, G -> semigroupFromGaps G))
LL = smallWeightSemigroups 8
netList for L in LL list syzFormat L
   






range={g,g+2,g+3,2*g+1,2*g+2}
elapsedTime testWeierstrassRange(L,range,Verbose=>true,Probably=>true)


g=5
netList apply(LL5=sort(findSemigroups g,L->ewt L),L->(gaps L,ewt L, weight L,L))
netList apply(LL5,L->(gaps L,syzFormat L))
L=LL6_1
I=semigroupIdeal L
gaps L
R=ring I
fI=res I
fI.dd_4
fI.dd_2
netList apply(gens R,x->(x,degree x))
m2x5=matrix{{x_3,x_0,x_2,x_4,x_1},
           {x_0^2,x_2,x_4, x_1,x_0*x_3}}
codim minors(2,m2x5), codim I
       minors(2,m2x5):I
trim ideal(gens I%minors(2,m2x5))m2x5b=matrix{{x_3,x_2,x_3,x_4,x_0^2},
             {x_1,x_3,x_4,x_0^2,x_1}}
gens trim(minors(2,m2x5)+minors(2,m2x5b))%I
gens I% trim minors(2,m2x5b))


LL = select(findSemigroups 4, L-> #L >2)
L = LL_1
(A,unfolding)= makeUnfolding(L);
numgens A
gens A/degree
b = optimalBound(L, 6, Verbose => true)
R = optimalRange(L, b, Verbose => true)
posList = prepareInitialPositionList(L, R, Verbose => true)
minLists = systematicShrinking(L,posList,Verbose => true,Probably => true)
minimalPositionLists (L, posList, 3, Verbose => true, Probably => true)
displayMinimalFamilies {(L, minlist_0)}

L = {3,5,7}
(A,unfolding) = makeUnfolding L;
flatteningRelations(semigroupIdeal L, A, unfolding)
transpose gens oo

LL = for g from 4 to 10 list (smallWeightSemigroups g)_0
netList LL
netList for L in LL_{0,1,2,3} list (
    (A,unfolding) = makeUnfolding L;
    factor numgens A, netList degreeArray (L, positionListToArray(
	           L,toList(0..numgens A-1))))
netList apply(LL, L -> gaps L)


smallWeightSemigroups g
LL = smallWeightSemigroups g
netList for L in LL list syzFormat L
(A,unfolding

LL = sort(findSemigroups 6, L -> ewt L)
netList for L in LL list (
    (A,unfolding) = makeUnfolding L;
    (L,ewt L, numgens A))
LL = reverse sort(LL, L -> (
     (A,unfolding) = makeUnfolding L;
    numgens A))

b7 = getFromDisk "bounds7"
#b7
bb = reverse sort(b7, b -> ewt b_0)
netList apply(bb, b -> (gaps b_0, ewt b_0, b_1, numgensA b_0, b_0))


biggensA = b -> (
    (A,unfolding) = makeUnfolding b_0;
    posList = prepareInitialPositionList(b_0, b_1);
    (B,eqns) = restrictedUnfolding(semigroupIdeal b_0, posList);
    numgens B)
netList apply(bb, b -> (gaps b_0, ewt b_0, b_1, numgensA b_0, biggensA b,  b_0))
run "ls -ltr"

biggensA 

    
    numgens A)


LL = {({6, 9, 13, 16}, true), ({8, 9, 12, 13}, true), ({8, 10, 13, 15}, true), ({8, 11, 12, 15}, true), ({8, 12, 13, 17}, true), ({8, 12, 15, 19}, true), ({9, 10, 14, 15}, true), ({10, 11, 15, 16}, true), ({10, 12, 15, 17},
       -----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
       true), ({10, 13, 15, 18}, true), ({10, 14, 15, 19}, true), ({10, 14, 17, 21}, true), ({11, 14, 18, 21}, true), ({14, 17, 21, 24}, true), ({14, 18, 21, 25}, true), ({15, 16, 18, 19}, true), ({15, 17, 21, 23}, true), ({15,
       -----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
       19, 21, 22}, true), ({19, 20, 22, 23}, true), ({19, 21, 25, 27}, true), ({19, 23, 24, 28}, true), ({23, 24, 26, 27}, true), ({23, 25, 29, 31}, true), ({24, 25, 28, 30}, true), ({24, 26, 29, 30}, true), ({27, 28, 30, 31},
       -----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
       true), ({27, 29, 33, 35}, true), ({28, 29, 32, 34}, true), ({28, 30, 33, 34}, true), ({30, 31, 34, 36}, true), ({30, 32, 35, 36}, true), ({31, 32, 34, 35}, true), ({31, 33, 37, 39}, true), ({34, 35, 38, 40}, true), ({34,
       -----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
       36, 39, 40}, true), ({35, 36, 38, 39}, true), ({35, 37, 41, 43}, true), ({36, 37, 40, 42}, true), ({36, 38, 41, 42}, true), ({39, 40, 42, 43}, true), ({39, 41, 45, 47}, true), ({40, 41, 44, 46}, true), ({40, 41, 45, 47},
       -----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
       true), ({40, 42, 45, 46}, true), ({40, 42, 46, 47}, true), ({42, 43, 46, 48}, true), ({42, 44, 47, 48}, true), ({43, 44, 46, 47}, true), ({43, 45, 49, 51}, true), ({45, 48, 50, 53}, true), ({46, 47, 50, 52}, true), ({46,
       -----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
       48, 51, 52}, true), ({47, 48, 50, 51}, true), ({47, 48, 52, 54}, true), ({47, 49, 53, 54}, true), ({47, 49, 53, 55}, true), ({48, 49, 52, 54}, true), ({48, 50, 53, 54}, true), ({50, 52, 55, 59}, true), ({50, 54, 57, 59},
       -----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
       true), ({51, 52, 54, 55}, true), ({51, 53, 57, 59}, true), ({52, 53, 56, 58}, true), ({52, 54, 57, 58}, true), ({53, 56, 58, 61}, true), ({54, 55, 58, 60}, true), ({54, 55, 59, 61}, true), ({54, 56, 59, 60}, true), ({54,
       -----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
       56, 60, 61}, true), ({55, 56, 58, 59}, true), ({55, 57, 61, 63}, true), ({58, 59, 62, 64}, true), ({58, 60, 63, 64}, true), ({59, 60, 62, 63}, true), ({59, 61, 64, 68}, true), ({59, 61, 65, 67}, true), ({59, 63, 66, 68},
       -----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
       true), ({60, 61, 64, 66}, true), ({60, 62, 65, 66}, true)}
LL0 = apply(LL, L -> L_0)
LL1 = testNWListOfLists LL0
A = toList(4..100);
B = toList(1..2);
C = toList(1..2);
D = toList(1..2);
netList (MM = flatten flatten flatten for a in A list(
    for b in B list(
     for c in C list(
      for d in D list(
	{a,a+b,a+b+c,a+b+c+d})))))
elapsedTime (tM = testNWListOfLists MM)
#tM
all apply (tM_{0..21}, L->dif1 L_0 =={1,2,1})


(b,c,d) = (1,2,1) -- a = 15+4n 4*binomial(n,2) +18*binomial (n,1) +33
(b,c,d) = (2,4,2) -- a = 15+4n
(b,c,d) = (3,6,3) -- a = 19 + 4,8,4,8,...
(b,c,d) = (4,8,4) -- a = 15+4n
(b,c,d) = (5,10,5) -- a = 19 + 4,4,4,8,4,4,4,8...
(b,c,d) = (6,12,6) -- a = 11+ 8,4,8,4,8...
(b,c,d) = (7,14,7) -- a = 11+4,4,4,4,4,8,4,4,4,4,4,8...
(b,c,d) = (8,16,8) -- a = 11+4n

p = 6
(b,c,d) = (2^p, 2^(p+1), 2^p) -- a = 11+4n for p = 3..6. 

(b,c,d) = (2,6,2) -- when b=d=1 or b= d=2 there seem to be just a couple,
--at least for c<=6, not twice b.

A = toList(4..100);
NN = for a in A list {a,a+b,a+b+c,a+b+c+d};
tN = testNWListOfLists NN;
tN
netList(tG = apply(tN, L -> semigroupGenus L_0))
d0 = tG_0
d1 = (dif1 tG)_0
d2 = (dif1 dif1 tG)_0
g = n-> d2*binomial(n,2)+d1*binomial (n,1) +d0
netList apply(#tG, i-> (tG_i, g i))

1,2,1
dif1 dif1 tG
g = n->4*binomial(n,1) +
apply(5 , n->g n)
dif1 tG
f = 
apply(6 , n->f n)
tG

middles = flatten for b from 1 to 10 list
                  for c from b+1 to 11 list (b,c)
LL = flatten for m in middles list(
     b := m_0;
     c := m_1;
     d := m_0;
     for a from 4 to 30 list {a,a+b,a+b+c,a+b+c+b});
tN = testNWListOfLists LL
(#tN+.0)/#LL -- about 10%
gN = for L in tN list (semigroupGenus L_0)
sort gN
(max gN)
(min gN)
#gN
--There are lots of gaps!

LL = apply(1000, i ->(
G = {6+random 100}|apply(3, i->random 100) ;
L = {L0= G_0, L1 = L0+G_1, L2 = L1+G_2, L3 = L2+G_3}));
elapsedTime apply(LL, L -> syzFormat L); --36 sec
elapsedTime (NL = apply(LL, L -> testNW L)); --40 secselect(NL, L->L_1)

------------------
L={6,9,13,16}




B=betti res semigroupIdeal L
A1=sum(keys B,k->(-1)^(k_0)*t^(k_2))
A1==A

///
-- continue g=12 bounds
restart
needsPackage "AIWeierstrass"
viewHelp "AIWeierstrass"
bounds12 = getFromDisk "bounds12";
#bounds12
tally apply(bounds12,D->D_1)
-*
o4 = Tally{4 => 1  }
           5 => 1
           6 => 6
           7 => 12
           8 => 34
           9 => 32
           10 => 26
           11 => 33
           12 => 29
           13 => 33
           14 => 17
           15 => 13
           16 => 4
           17 => 13
           18 => 1
           19 => 4
           20 => 2
           21 => 1
           25 => 1
           26 => 2
           27 => 1


*-

LL12sorted = value get "LL12sorted";
#LL12sorted
LLb12=apply(bounds12,D->D_0);
pos=positions(LL12sorted, L->not member(L,LLb12))
LL12sorteda=LL12sorted_{0..106,108..157,159..164,166..198,
    200..209,211..226,228..233,235..252,254..256,258..266,268..275,277..344,
    107,158,165,199,210,227,234,253,257,267,276};
last bounds12

bounds12a=continueComputation(produceBounds,LL12sorteda,"bounds12",Verbose=>true);


restart
needsPackage "AIWeierstrass"
LLdifficult={{6, 8, 17, 19, 21},
    {6, 8, 10, 19, 21, 23},
    {8, 9, 11, 15, 21}}
L=first LLdifficult
#gaps L
def1 L
elapsedTime testWeierstrass(L,8,Verbose=>true)
-*
time to decompose the base = 
 -- .425137s elapsed
number of components = 4
behavior of components ={0, 0, 0, 0}
 -- 25.1962s elapsed

o8 = 0
*-
range={4,8,12,16,20,24,28,32,36,40}
elapsedTime testWeierstrass(L,range,Verbose=>true)

-*
-- 2.41907s elapsed

o15 = 0
*-
elapsedTime testWeierstrass(L,3,Verbose=>true)

I=semigroupIdeal L
S=ring I
fI=res I
fI.dd_4
apply(gens S,m->(m,degree m))
m2x3=matrix{{x_0,x_5,x_1},
            {x_2,x_1,x_3}}
J=minors(2, m2x3)
ideal(gens I%J)
kunz=ideal (gens I%x_0)
kk=coefficientRing S
R=kk[support kunz]
betti(fKunz=res (kunz=trim sub(kunz,R)))
fKunz.dd_4
res ideal fKunz.dd_1_{1..9}

-- can we restrict the variables somewhat by considering the last two matrices
L=(last bounds12)_0
L={6, 9, 17, 19, 20, 22}
ms=degreeMatrices L;#ms
degsmc=sort unique flatten entries last ms
degsmc=sort unique flatten entries ms_(#L-2)
degsmc'=sort unique flatten entries ms_(#L-3)
I=semigroupIdeal L;
(A,unfolding)=makeUnfolding I;
#select(gens A, a-> member((degree a)_0,degsmc))
#gens A
sort unique apply(gens A,a->(degree a)_0)
betti last ms
betti ms_(#L-3)
24*45+24*5
numgens A
---- end of last two matrices thought
  

restart
needsPackage "AIWeierstrass"
elapsedTime ans=apply(1000,i->(
	(a,b,c)=(1+random(100),1+random(100),1+random(100));
	testNW(a,b,c,b)));
first ans
tally apply(ans,D->D_1)

LLh = toList value get "LLh45-15-30-15s";
netList LLh_{0..1}
viewHelp addData


viewHelp "AIWeierstrass"

r1=toList(6..25)
r2=toList(1..5)
r3=toList(1..10)
r4=toList(1..5)

elapsedTime  LL = flatten flatten flatten for a in r1 list
    for b in r2 list
     for c in r3 list
      for d in r4 list(
	L = {a,a+b,a+b+c,a+b+c+d};
	if gcd L !=1 or #minimalSemigroupGens L!= 4 then continue;
	I=semigroupIdeal L;
	fI=res I;
	if apply(4,i->rank fI_i)!= {1,4,6,3} then continue;
	if not min (flatten degrees fI_2)_{4,5} > (degrees fI_3)_0_0 then continue;
	L);
#LL	
LL=sort(LL,L->#gaps L)	
netList reverse apply(LL,L->(I=semigroupIdeal L;
	fI=res I;
	formatL=apply(4,i->rank fI_i);
	(L,#gaps L,formatL,fI.dd_3_{0},degrees fI_3)))	



L= LL_0 -- the section is the origin
L=={16, 19, 21, 22}
I=semigroupIdeal L
(A,unfolding)=makeUnfolding I;
numgens A
testWeierstrass(L,4,Verbose=>true)
elapsedTime b=optimalBound(L,4,Verbose=>true)
elapsedTime range=optimalRange(L,21,Verbose=>true)
elapsedTime range1=shrinkRange(L,range,Verbose=>true)
initialList=prepareInitialPositionList(L,range1,Verbose=>true)
elapsedTime minLists=minimalPositionLists(L,range1,3,Verbose=>true)
displayMinimalFamilies apply(minLists,pos->(L,pos))
(J,family,runfolding,J1)=showRestrictedFamily(L,minLists_0);
betti J
fF=res ideal family
fF.dd_3_{0}
fF.dd_2
fiber=getFiber(L,minLists_0)
dimSingularLocusOfFiber(fiber)
gens fiber%ideal vars ring fiber==0 

--Generic example
--Given a resolution 1 -> 4 -> 4 -> 1
of kka,b,c,d]/If
where If = (f1..f4) and
the fi are all irreducible
and the left hand matrix is the
column of vars and the middle matrix
has the form
* * 0 0
* * * *
* * * *
0 0 * *
It follows from the irreduibility of the f_i
that the two elements in the top row
are a regular sequence, and the same for the
bottom. Since the rows are relations on the
variables the matrix phi must be
b -a 0  0
*  * *  *
*  * *  *
0  0 d -c
This matrix must be a composition of the koszul
6x 4 matrix with some 4 x 6 matrix!

Note that the four rows of phi
must be combinations of the 6 rows
of the 6x4 Koszul matrix

kappa = 
| -b a  0  0 |
| -c 0  a  0 |
| 0  -c b  0 |
| -d 0  0  a |
| 0  -d 0  b |
| 0  0  -d c |

Since the first and lost rows of phi agree
with those of kappa we can, after linear trans,
assume that 
phi = T*kappa, where

T = 
1 0 0 0 0 0
0 * * * * 0
0 * * * * 0
0 0 0 0 0 1

///
restart
kk = ZZ/101
S = kk[a..d,A..H]
T = matrix"1"++
matrix"A,B,C,D;E,F,G,H"++
matrix"1"

kappa = matrix"
 -b, a,  0,  0;
 -c, 0,  a,  0; 
 0 , -c, b , 0 ;
 -d, 0,  0 , a ;
 0 , -d, 0 , b ;
 0,  0,  -d, c
 "
phi = T*kappa
0==phi * transpose matrix"a,b,c,d"
(phi_{0,1}, phi_{2,3})
If = minors(2, phi_{0,1})+ minors(2, phi_{2,3})
radical If == If
#decompose If
res If
isSubset(If, (ideal(a,b,c,d))^2)

---
needsPackage "AIWeierstrass"
L = {6,9,13,16}
fL = res semigroupIdeal L
fL.dd_2
fL.dd_3
gaps L
LL = toList value get "LLh45-15-30-15s";
LL_0_0
L = LL_1_0
gaps L
degrees source (res semigroupIdeal L).dd_3
L
lastGaps =  L -> (
    G := gaps L;
    G_{#G-2, #G-1}
    )
lastGaps L
#LL
LLodd = select (LL, L -> (
	LG =lastGaps L_0;
	(min L_0) == (LG_1-LG_0)
	));
L = LLodd_0_0
semigroupGenus L
gaps L
lastGaps L

can = L -> (
    G = gaps L;
    F = max G;
    s = sum L;
    drop(apply(G, h-> F-h-1),-1)
)    
minimalSemigroupGens can L
gaps L
L
sum L
lastGaps L
om = L -> (
    G := gaps L;
    c := max G +1;
    om1 := apply(G, h-> sum L -h+1);
    R := semigroupRing L;
    om2 := apply(om1, i -> random(i,R));
    om3 := trim ideal om2;
    reverse apply(om3/degree, d -> F - (d_0-F-1))
    )
om L
    code methods findSemigroups
L = LLodd_2_0
om L

specialGaps = L -> (
    G := gaps L;
    F := max G;
    S := (apery L)#"semigroup";
    select(G, h -> all for ell in L list(
	       h+ell > F or isMember(h+ell, S))
    ))
fourRelations = L ->(
    A := apery L;
    S := A#"semigroup";
    c := A#"conductor";
    G := gaps L;
    sg := specialGaps L;
    F = max G;
    sg = reverse apply(sg, h -> F -h);
    candidates := for ell in L list for g in sg list
         (g,ell);
    flatten candidates
    )
netList fourRelations L
L
tally apply(LL_{100..200}, ell -> #specialGaps ell_0)
L = LL_200_0
specialGaps L
om L

specialGaps {3,5,7}    
gaps{3,5,7}
betti res semigroupIdeal{3,5,7}

-- lift to characterisyic zero
restart
needsPackage "AIWeierstrass"
g=8
LL=select(findSemigroups g,L->not knownExample L and min L >5);
#LL
LL
elapsedTime LLb=produceBounds(LL,"bounds8") -- 160.796s elapsed
elapsedTime LLR=produceRangesFromBounds(LLb,"ranges8") -- 282.315s elapsed
elapsedTime LLSR=produceShrinkedRangesFromRanges(LLR,"shrinkedRanges8")  -- 52.3814s elapsed
elapsedTime LLMinLists=flatten produceMinListsFromRanges(LLSR,2,"minLists8") -- 424.999s elapsed
elapsedTime LLMinFamilies=produceMinimalFamiliesFromMinLists(LLMinLists,"minFams8")

elapsedTime tally apply(#LLMinFamilies,i->(D=LLMinFamilies_i;L=D_0;fam=D_1;J=D_2;
	<<" case = "<< i <<", semigroup = "<< L<<flush <<endl;
	elapsedTime answer=liftToCharacteristicZero(L,fam,J);
        <<endl;
	(L,answer))) -- .918969s elapsed
-*
o31 = Tally{({6, 7, 8, 17}, true) => 2     }
            ({6, 7, 9, 17}, true) => 1
            ({6, 8, 9, 10}, true) => 1
            ({6, 8, 9, 11}, true) => 1
            ({6, 8, 10, 11, 13}, true) => 1
            ({7, 8, 9, 10, 11}, true) => 2
            ({7, 8, 9, 10, 12}, true) => 2
            ({7, 8, 9, 10, 13}, true) => 1
            ({7, 8, 9, 11, 12}, true) => 1
*-
g=9
LL=select(findSemigroups g,L->not knownExample L and min L >5);
#LL
LL
elapsedTime LLb=produceBounds(LL,"bounds9");  -- 1056.29s elapsed
LLb=unique getFromDisk "bounds9"
LLb1=select(LLb,Lb->member(Lb_0,LL))
#unique LLb1
tally apply(LLb1,Lb->Lb_0)
tally LLb1
elapsedTime LLR=produceRangesFromBounds(LLb1,"ranges9"); -- 3610.66s elapsed
#unique LLR,#LLR
LLRa=continueComputation(produceRangesFromBounds,LLb,"ranges9")
LLRb=getFromDisk ranges9;#LLRb
elapsedTime LLSR=produceShrinkedRangesFromRanges(LLR,"shrinkedRanges9");  -- 1042.37s elapsed
toString LLSR
LLSR={({8, 9, 10, 11, 12, 13},{12, 13, 14}), ({7, 8, 9, 10},{21}), ({8, 9, 10, 11, 12, 14},{10, 12,
       14}), ({7, 8, 9, 11},{8, 10, 11}), ({7, 9, 10, 11, 12},{12, 13}), ({6, 8, 10, 13, 15},{12, 15,
       18}), ({6, 8, 10, 11},{12, 14}), ({8, 9, 10, 11, 13, 14},{8, 9, 11}), ({8, 9, 10, 11, 12,
       15},{10, 11, 12}), ({7, 8, 10, 11},{14, 16, 30}), ({7, 8, 9, 12},{9, 12, 18}), ({7, 9, 10, 11,
       13},{9, 13}), ({6, 9, 10, 13, 14},{12, 14}), ({6, 8, 9, 19},{12, 18, 30}), ({6, 8, 10, 13,
       17},{10, 13, 14, 16, 24}), ({6, 7, 11, 15},{12, 15}), ({6, 9, 10, 11},{12}), ({8, 9, 10, 12,
       13, 14},{7, 9, 14, 16}), ({8, 9, 10, 11, 13, 15},{9, 10, 11, 13}), ({7, 9, 10, 11, 15},{9, 10,
       11}), ({7, 8, 10, 12},{14, 16}), ({7, 8, 9, 13, 19},{19, 20}), ({7, 9, 10, 12, 13},{13, 14}),
       ({7, 8, 11, 12, 13},{11, 13}), ({7, 9, 11, 12, 13, 15},{12, 13, 14, 15}), ({6, 8, 10, 15, 17,
       19},{12, 13, 14, 18, 19, 21, 24, 26}), ({6, 9, 10, 13, 17},{9, 13, 17, 21}), ({6, 9, 11, 13,
       14},{9, 12, 13}), ({6, 7, 11, 16},{21}), ({6, 8, 11, 13},{16, 18}), ({7, 8, 9, 12},{9, 12,
       18}), ({8, 9, 10, 11, 13, 15},{10, 15, 20}), ({8, 9, 10, 12, 13, 14},{7, 9, 14, 16}), ({8, 9,
       10, 11, 13, 14},{8, 9, 11})}

elapsedTime LLMinLists=flatten produceMinListsFromRanges(LLSR,2,"minLists9");-- 7047.15s elapsed
toString LLMinLists

LLMinLists={({8, 9, 10, 11, 12, 13},{20, 31, 42, 54, 55, 67, 80, 81, 94, 109, 110, 123, 124, 125, 139, 140,
     156, 157}), ({7, 8, 9, 10},{25, 45, 66}), ({8, 9, 10, 11, 12, 14},{1, 33, 45, 99, 111, 127, 144,
     146, 162}), ({8, 9, 10, 11, 12, 14},{1, 22, 54, 67, 71, 81, 96, 162}), ({7, 8, 9, 11},{2, 8, 9,
     20, 38, 40}), ({7, 9, 10, 11, 12},{20, 44, 56, 71, 86}), ({7, 9, 10, 11, 12},{10, 20, 32, 56, 57,
     86}), ({6, 8, 10, 13, 15},{9, 19, 29, 42, 57, 59, 72, 90, 92, 110, 113}), ({6, 8, 10, 11},{8, 18,
     29, 30}), ({8, 9, 10, 11, 13, 14},{2, 23, 33, 59, 74, 102, 104, 118, 120, 137, 155, 174}), ({8,
     9, 10, 11, 13, 14},{2, 3, 13, 23, 33, 48, 59, 74, 102, 104, 118, 137, 155}), ({8, 9, 10, 11, 12,
     15},{1, 33, 45, 70, 85, 116, 170}), ({7, 8, 10, 11},{10, 23, 36, 53, 67, 72}), ({7, 8, 9,
     12},{11, 23, 25, 36, 39, 54, 57}), ({7, 8, 9, 12},{1, 10, 23, 25, 42, 54}), ({7, 9, 10, 11,
     13},{2, 21, 48, 74, 90}), ({6, 9, 10, 13, 14},{1, 33, 60, 78, 94, 113}), ({6, 8, 9, 19},{1, 10,
     43, 65, 79, 88, 94}), ({6, 8, 9, 19},{1, 10, 13, 43, 46, 65, 79, 88}), ({6, 8, 10, 13, 17},{1,
     19, 30, 45, 60, 61, 62, 64, 80, 82, 98, 99, 100, 103, 116, 125, 128}), ({6, 7, 11, 15},{1, 23,
     40, 58, 60}), ({6, 9, 10, 11},{1, 22, 35}), ({8, 9, 10, 12, 13, 14},{2, 14, 37, 75, 80, 88, 90,
     111, 121, 126, 138, 145, 157, 163, 174, 176}), ({8, 9, 10, 12, 13, 14},{2, 14, 33, 37, 46, 60,
     80, 88, 111, 121, 122, 126, 138, 139, 145, 163, 174, 176}), ({8, 9, 10, 11, 13, 15},{2, 23, 58,
     73, 90, 120, 140, 176}), ({7, 9, 10, 11, 15},{1, 2, 12, 13, 23, 36, 50, 51, 82, 83, 104}), ({7,
     9, 10, 11, 15},{1, 2, 11, 12, 24, 36, 65, 66, 82, 84, 105}), ({7, 8, 10, 12},{13, 27, 41, 42, 57,
     75, 76}), ({7, 8, 9, 13, 19},{50, 86, 125, 154}), ({7, 8, 9, 13, 19},{33, 68, 105, 154}), ({7, 9,
     10, 12, 13},{11, 22, 35, 63, 96, 113}), ({7, 8, 11, 12, 13},{23, 36, 50, 80, 94, 111}), ({7, 9,
     11, 12, 13, 15},{21, 22, 33, 34, 46, 47, 60, 61, 74, 75, 90, 91, 105, 107, 121, 123, 139, 140,
     156, 157, 158, 159, 176, 177, 196, 197}), ({7, 9, 11, 12, 13, 15},{10, 21, 33, 46, 47, 60, 74,
     90, 91, 105, 106, 121, 123, 139, 140, 141, 156, 157, 176, 178, 196, 197, 198}), ({6, 8, 10, 15,
     17, 19},{8, 18, 42, 58, 75, 93, 97, 112, 117, 130, 136, 152, 159, 161, 179, 204, 209, 211, 226,
     227, 231, 238, 254, 255, 260, 267}), ({6, 9, 10, 13, 17},{2, 10, 12, 21, 33, 35, 48, 51, 54, 65,
     81, 83, 89, 103, 106, 110, 121, 124, 127, 131, 145, 148, 152}), ({6, 9, 11, 13, 14},{2, 12, 50,
     83, 86, 101, 104, 123}), ({6, 9, 11, 13, 14},{2, 25, 39, 50, 54, 83, 101, 104}), ({6, 7, 11,
     16},{37, 56, 76}), ({6, 8, 11, 13},{11, 25, 39, 55, 73, 75}), ({7, 8, 9, 12},{11, 23, 25, 36, 39,
     54, 57}), ({7, 8, 9, 12},{1, 10, 23, 25, 42, 54}), ({8, 9, 10, 11, 13, 15},{1, 22, 56, 71, 105,
     119, 158, 171, 174, 179}), ({8, 9, 10, 12, 13, 14},{2, 14, 37, 75, 80, 88, 90, 111, 121, 126,
     138, 145, 157, 163, 174, 176}), ({8, 9, 10, 11, 13, 14},{2, 23, 33, 59, 74, 102, 104, 118, 120,
     137, 155, 174}), ({8, 9, 10, 11, 13, 14},{2, 3, 13, 23, 33, 48, 59, 74, 102, 104, 118, 137,
     155})}


elapsedTime LLMinFamilies=produceMinimalFamiliesFromMinLists(LLMinLists,"minFams9");


elapsedTime tally apply(#LLMinFamilies,i->(D=LLMinFamilies_i;L=D_0;fam=D_1;J=D_2;
	<<" case = "<< i <<", semigroup = "<< L<<flush <<endl;
	elapsedTime answer=liftToCharacteristicZero(L,fam,J);
        <<endl;
	(L,answer)))

 -- 8.59376s elapsed

o4 = Tally{({6, 7, 11, 15}, true) => 1        }
           ({6, 7, 11, 16}, true) => 1
           ({6, 8, 9, 19}, true) => 2
           ({6, 8, 10, 11}, true) => 1
           ({6, 8, 10, 13, 15}, true) => 1
           ({6, 8, 10, 13, 17}, true) => 1
           ({6, 8, 10, 15, 17, 19}, true) => 1
           ({6, 8, 11, 13}, true) => 1
           ({6, 9, 10, 11}, true) => 1
           ({6, 9, 10, 13, 14}, true) => 1
           ({6, 9, 10, 13, 17}, true) => 1
           ({6, 9, 11, 13, 14}, true) => 2
           ({7, 8, 9, 10}, true) => 1
           ({7, 8, 9, 11}, true) => 1
           ({7, 8, 9, 12}, true) => 4
           ({7, 8, 9, 13, 19}, true) => 2
           ({7, 8, 10, 11}, true) => 1
           ({7, 8, 10, 12}, true) => 1
           ({7, 8, 11, 12, 13}, true) => 1
           ({7, 9, 10, 11, 12}, true) => 2
           ({7, 9, 10, 11, 13}, true) => 1
           ({7, 9, 10, 11, 15}, true) => 2
           ({7, 9, 10, 12, 13}, true) => 1
           ({7, 9, 11, 12, 13, 15}, true) => 2
           ({8, 9, 10, 11, 12, 13}, true) => 1
           ({8, 9, 10, 11, 12, 14}, true) => 2
           ({8, 9, 10, 11, 12, 15}, true) => 1
           ({8, 9, 10, 11, 13, 14}, true) => 4
           ({8, 9, 10, 11, 13, 15}, true) => 2
           ({8, 9, 10, 12, 13, 14}, true) => 3
#keys o4

toString LLMinFamilies

-- the next needs an editing because of bad line breaks
LLMinFamilies1={({8, 9, 10, 11, 12, 13},matrix {{x_1^2-x_0*x_2, x_1*x_2-x_0*x_3, x_1*x_3-x_0*x_4+x_0*a_{2, 1},
     x_2^2-x_0*x_4+x_0*a_{2, 1}, x_1*x_4-x_0*x_5+x_0*a_{4, 1}, x_2*x_3-x_0*x_5+x_0*a_{4, 1}+x_1*a_{2,
     1}, x_2*x_4-x_1*x_5+x_1*a_{4, 1}, x_3^2-x_1*x_5+x_1*a_{4, 1}+x_2*a_{2, 1},
     x_3*x_4-x_2*x_5+x_2*a_{4, 1}, x_4^2-x_3*x_5+x_3*a_{4, 1}-x_4*a_{2, 1}, x_0^3-x_3*x_5+x_2*a_{10,
     3}+x_3*a_{10, 4}-x_4*a_{2, 1}, x_0^2*x_1-x_4*x_5+x_3*a_{10, 3}+x_4*a_{10, 4},
     x_0^2*x_2-x_5^2+x_4*a_{10, 3}+x_5*a_{10, 4}+x_5*a_{4, 1}}},ideal(a_{10, 4}*a_{2, 1}-a_{4,
     1}*a_{2, 1},a_{10, 4}*a_{4, 1}+a_{10, 3}*a_{2, 1})), ({7, 8, 9, 10},matrix {{x_1^2-x_0*x_2,
     x_1*x_2-x_0*x_3, x_2^2-x_1*x_3, x_0^4-x_1*x_3^2+x_0*a_{3, 1}, x_0^3*x_1-x_2*x_3^2+x_1*a_{3, 1},
     x_0^3*x_2-x_3^3+x_2*a_{3, 1}}},ideal()), ({8, 9, 10, 11, 12, 14},matrix {{x_1^2-x_0*x_2+x_0*a_{0,
     1}, x_1*x_2-x_0*x_3, x_1*x_3-x_0*x_4, x_2^2-x_0*x_4-x_2*a_{0, 1}, x_2*x_3-x_1*x_4-x_3*a_{0, 1},
     x_2*x_4-x_0*x_6, x_3^2-x_0*x_6, x_3*x_4-x_1*x_6, x_4^2-x_2*x_6+x_6*a_{0, 1},
     x_0^3-x_2*x_6+x_2*a_{9, 3}, x_0^2*x_1-x_3*x_6+x_3*a_{9, 3}, x_0^2*x_2-x_4*x_6+x_4*a_{9,
     3}-x_0^2*a_{0, 1}, x_0^2*x_4-x_6^2+x_6*a_{9, 3}}},ideal()), ({8, 9, 10, 11, 12, 14},matrix
     {{x_1^2-x_0*x_2+x_0*a_{0, 1}, x_1*x_2-x_0*x_3, x_1*x_3-x_0*x_4+x_2*a_{0, 1}, x_2^2-x_0*x_4,
     x_2*x_3-x_1*x_4, x_2*x_4-x_0*x_6+x_0*a_{5, 1}, x_3^2-x_0*x_6+x_0*a_{5, 1}+x_4*a_{0, 1},
     x_3*x_4-x_1*x_6+x_1*a_{5, 1}, x_4^2-x_2*x_6+x_2*a_{5, 1}, x_0^3-x_2*x_6, x_0^2*x_1-x_3*x_6,
     x_0^2*x_2-x_4*x_6, x_0^2*x_4-x_6^2+x_6*a_{5, 1}}},ideal()), ({7, 8, 9, 11},matrix
     {{x_1^2-x_0*x_2+x_1*a_{0, 2}, x_2^2-x_0*x_4+x_0*a_{1, 1}+x_1*a_{1, 2}, x_0^2*x_1-x_4^2+x_4*a_{1,
     1}, x_0^4-x_1*x_2*x_4-x_0*x_4*a_{1, 2}-x_2*x_4*a_{0, 2}}},ideal()), ({7, 9, 10, 11, 12},matrix
     {{x_2^2-x_0*x_4, x_2*x_3-x_0*x_5, x_3^2-x_2*x_4+x_0*a_{2, 1}, x_3*x_4-x_2*x_5,
     x_0^3-x_2*x_5+x_2*a_{4, 2}, x_4^2-x_3*x_5-x_2*a_{2, 1}, x_0^2*x_2-x_4*x_5+x_4*a_{4, 2},
     x_0^2*x_3-x_5^2+x_5*a_{4, 2}}},ideal()), ({7, 9, 10, 11, 12},matrix {{x_2^2-x_0*x_4,
     x_2*x_3-x_0*x_5+x_0*a_{1, 1}, x_3^2-x_2*x_4+x_0*a_{2, 1}, x_3*x_4-x_2*x_5+x_2*a_{1, 1},
     x_0^3-x_2*x_5, x_4^2-x_3*x_5-x_2*a_{2, 1}+x_3*a_{1, 1}, x_0^2*x_2-x_4*x_5,
     x_0^2*x_3-x_5^2+x_5*a_{1, 1}}},ideal()), ({6, 8, 10, 13, 15},matrix {{x_2^2-x_0*x_4,
     x_0^3-x_2*x_4+x_0*a_{1, 1}, x_0^2*x_2-x_4^2+x_2*a_{1, 1}, x_2*x_1-x_0*x_3+x_0*a_{3, 1},
     x_4*x_1-x_2*x_3+x_2*a_{3, 1}, x_0^2*x_1-x_4*x_3+x_4*a_{3, 1}+x_1*a_{1, 1},
     x_0*x_4^2-x_1^2+x_2*a_{6, 2}, x_2*x_4^2-x_1*x_3+x_4*a_{6, 2}+x_1*a_{3, 1},
     x_4^3-x_3^2+x_0^2*a_{6, 2}+2*x_3*a_{3, 1}}},ideal(a_{3, 1}^2-a_{6, 2}*a_{1, 1})), ({6, 8, 10,
     11},matrix {{x_2^2-x_0*x_4, x_0^3-x_2*x_4+x_0*a_{1, 1}, x_0^2*x_2-x_4^2+x_2*a_{1, 1},
     x_0^2*x_4-x_5^2+x_2*a_{3, 2}+x_4*a_{3, 3}}},ideal()), ({8, 9, 10, 11, 13, 14},matrix
     {{x_1^2-x_0*x_2+x_1*a_{0, 2}, x_1*x_2-x_0*x_3, x_2^2-x_1*x_3-x_3*a_{0, 2},
     x_2*x_3-x_0*x_5+x_2*a_{3, 3}, x_1*x_5-x_0*x_6, x_3^2-x_0*x_6+x_3*a_{3, 3},
     x_2*x_5-x_1*x_6-x_6*a_{0, 2}, x_3*x_5-x_2*x_6, x_0^3-x_2*x_6-x_5*a_{3, 3}+x_0^2*a_{8, 7},
     x_0^2*x_1-x_3*x_6-x_6*a_{3, 3}+x_0*x_1*a_{8, 7}, x_0^2*x_2-x_5^2+x_0*x_2*a_{8, 7},
     x_0^2*x_3-x_5*x_6+x_0*x_3*a_{8, 7}, x_0*x_1*x_3-x_6^2+x_1*x_3*a_{8, 7}}},ideal()), ({8, 9, 10,
     11, 13, 14},matrix {{x_1^2-x_0*x_2+x_1*a_{0, 2}+x_2*a_{0, 3}, x_1*x_2-x_0*x_3+x_3*a_{0, 3},
     x_2^2-x_1*x_3-x_3*a_{0, 2}, x_2*x_3-x_0*x_5+x_2*a_{3, 3}, x_1*x_5-x_0*x_6+x_6*a_{0, 3},
     x_3^2-x_0*x_6+x_3*a_{3, 3}, x_2*x_5-x_1*x_6-x_6*a_{0, 2}, x_3*x_5-x_2*x_6,
     x_0^3-x_2*x_6-x_5*a_{3, 3}-x_0^2*a_{0, 3}, x_0^2*x_1-x_3*x_6-x_6*a_{3, 3},
     x_0^2*x_2-x_5^2-x_0*x_2*a_{0, 3}, x_0^2*x_3-x_5*x_6-x_0*x_3*a_{0, 3},
     x_0*x_1*x_3-x_6^2}},ideal()), ({8, 9, 10, 11, 12, 15},matrix {{x_1^2-x_0*x_2+x_0*a_{0, 1},
     x_1*x_2-x_0*x_3, x_1*x_3-x_0*x_4, x_2^2-x_0*x_4-x_2*a_{0, 1}, x_2*x_3-x_1*x_4-x_3*a_{0, 1},
     x_3^2-x_2*x_4, x_3*x_4-x_0*x_7+x_3*a_{6, 4}, x_4^2-x_1*x_7+x_4*a_{6, 4}, x_0^3-x_1*x_7,
     x_0^2*x_1-x_2*x_7+x_7*a_{0, 1}, x_0^2*x_2-x_3*x_7, x_0^2*x_3-x_4*x_7,
     x_0*x_2*x_4-x_7^2+x_0*x_2*a_{6, 4}}},ideal()), ({7, 8, 10, 11},matrix {{x_1*x_3-x_0*x_4,
     x_0^3-x_3*x_4+x_0*a_{1, 1}, x_0^2*x_1-x_4^2+x_1*a_{1, 1}, x_1^3-x_0^2*x_3+x_1*a_{3, 2},
     x_0*x_3^2-x_1^2*x_4-x_4*a_{3, 2}, x_3^3-x_1*x_4^2-x_0^2*a_{3, 2}-a_{3, 2}*a_{1, 1}}},ideal()),
     ({7, 8, 9, 12},matrix {{x_1^2-x_0*x_2, x_0^3-x_2*x_5+x_5*a_{1, 4}, x_0*x_1*x_2-x_5^2+x_5*a_{2,
     4}+x_0*x_1*a_{1, 4}, x_1*x_2^2-x_0^2*x_5+x_0^2*a_{2, 4}-x_1*a_{1, 4}^2,
     x_2^3-x_0*x_1*x_5+x_0*x_1*a_{2, 4}-x_2*a_{1, 4}^2}},ideal()), ({7, 8, 9, 12},matrix
     {{x_1^2-x_0*x_2+x_0*a_{0, 1}, x_0^3-x_2*x_5+x_2*a_{1, 3}, x_0*x_1*x_2-x_5^2+x_5*a_{1,
     3}+x_0*x_1*a_{0, 1}, x_1*x_2^2-x_0^2*x_5+x_1*x_2*a_{0, 1}, x_2^3-x_0*x_1*x_5-x_2*a_{0,
     1}^2}},ideal()), ({7, 9, 10, 11, 13},matrix {{x_2^2-x_0*x_4+x_2*a_{0, 2}, x_2*x_4-x_0*x_6,
     x_3^2-x_0*x_6+x_0*a_{2, 1}, x_0^3-x_3*x_4, x_4^2-x_2*x_6-x_6*a_{0, 2}, x_0^2*x_2-x_3*x_6,
     x_0^2*x_3-x_4*x_6+x_4*a_{2, 1}, x_0*x_2*x_3-x_6^2+x_6*a_{2, 1}}},ideal()), ({6, 9, 10, 13,
     14},matrix {{x_0^3-x_3^2+x_0*a_{0, 1}, x_3*x_4-x_0*x_1, x_4^2-x_0*x_2,
     x_0^2*x_4-x_3*x_1+x_4*a_{0, 1}, x_4*x_1-x_3*x_2, x_0*x_3^2-x_4*x_2+x_4*a_{5, 3},
     x_1^2-x_0^2*x_2-x_2*a_{0, 1}, x_3^3-x_1*x_2+x_1*a_{5, 3}, x_0*x_3*x_1-x_2^2+x_2*a_{5,
     3}}},ideal()), ({6, 8, 9, 19},matrix {{x_0^3-x_3^2+x_0*a_{0, 1}, x_2^3-x_0*x_3^2+x_0*a_{1, 1},
     x_2^2*x_3-x_0*x_1, x_3^3-x_2*x_1-x_3*a_{1, 1}, x_0^2*x_2^2-x_3*x_1+x_2^2*a_{0, 1},
     x_0^2*x_2*x_3^2-x_1^2-x_0^2*x_2*a_{1, 1}+x_2*x_3^2*a_{0, 1}-x_2*a_{1, 1}*a_{0, 1}}},ideal()),
     ({6, 8, 9, 19},matrix {{x_0^3-x_3^2+x_0*a_{0, 1}, x_2^3-x_0*x_3^2+x_0*a_{1, 1}+x_0^2*a_{0, 1},
     x_2^2*x_3-x_0*x_1, x_3^3-x_2*x_1-x_3*a_{1, 1}-x_0*x_3*a_{0, 1}, x_0^2*x_2^2-x_3*x_1+x_2^2*a_{0,
     1}, x_0^2*x_2*x_3^2-x_1^2-x_0^2*x_2*a_{1, 1}-x_2*a_{1, 1}*a_{0, 1}}},ideal()), ({6, 8, 10, 13,
     17},matrix {{x_2^2-x_0*x_4+x_0*a_{0, 1}, x_0^3-x_2*x_4, x_0^2*x_2-x_4^2+x_4*a_{0, 1},
     x_4*x_1-x_0*x_5+x_4*a_{3, 3}, x_0^2*x_1-x_2*x_5+x_0^2*a_{3, 3}, x_0*x_4^2-x_1^2+x_4*a_{5,
     3}+x_0^2*a_{5, 4}+x_1*a_{5, 5}+x_0*x_4*a_{5, 7}, x_0*x_2*x_1-x_4*x_5+x_0*x_2*a_{3, 3}+x_5*a_{0,
     1}, x_4^3-x_1*x_5+x_0*x_2*a_{5, 3}+x_0*x_4*a_{5, 4}+x_5*a_{5, 5}+x_5*a_{3, 3}+x_4^2*a_{5, 7},
     x_2*x_1^2-x_5^2+2*x_2*x_1*a_{3, 3}+x_0*x_2*x_4*a_{0, 1}+x_4*a_{5, 4}*a_{0, 1}}},ideal(a_{5,
     7}*a_{0, 1}+a_{0, 1}^2,a_{5, 5}*a_{0, 1}+2*a_{3, 3}*a_{0, 1},a_{3, 3}^2+a_{5, 3}*a_{0, 1},a_{5,
     5}*a_{3, 3}-2*a_{5, 3}*a_{0, 1})), ({6, 7, 11, 15},matrix {{x_0^3-x_1*x_5+x_0*a_{0, 1},
     x_1^3-x_0*x_3, x_5^2-x_1*x_3+x_1*a_{2, 2}, x_0^2*x_1^2-x_5*x_3+x_1^2*a_{0, 1},
     x_0^2*x_1*x_5-x_3^2+x_3*a_{2, 2}+x_1*x_5*a_{0, 1}}},ideal()), ({6, 9, 10, 11},matrix
     {{x_0^3-x_3^2+x_0*a_{0, 1}, x_4^2-x_3*x_5, x_0^2*x_3-x_4*x_5+x_3*a_{2, 2},
     x_0^2*x_4-x_5^2+x_4*a_{2, 2}}},ideal()), ({8, 9, 10, 12, 13, 14},matrix {{x_1^2-x_0*x_2+x_1*a_{0,
     2}, x_2^2-x_0*x_4+x_5*a_{1, 5}, x_1*x_4-x_0*x_5, x_1*x_5-x_0*x_6+x_5*a_{0, 2}, x_2*x_4-x_0*x_6,
     x_2*x_5-x_1*x_6, x_4^2-x_2*x_6-x_0*x_1*a_{1, 5}-x_2*a_{1, 5}^2, x_0^3-x_2*x_6+x_0*a_{0, 2}*a_{1,
     5}-x_2*a_{1, 5}^2, x_0^2*x_1-x_4*x_5+x_0*x_2*a_{1, 5}, x_5^2-x_4*x_6+x_0*x_1*a_{0, 2}+x_2*a_{0,
     2}*a_{1, 5}, x_0^2*x_2-x_4*x_6+x_1*x_2*a_{1, 5}+x_2*a_{0, 2}*a_{1, 5},
     x_0*x_1*x_2-x_5*x_6+x_0*x_4*a_{1, 5}-x_5*a_{1, 5}^2, x_0^2*x_4-x_6^2+x_4*a_{0, 2}*a_{1,
     5}-x_6*a_{1, 5}^2}},ideal()), ({8, 9, 10, 12, 13, 14},matrix {{x_1^2-x_0*x_2+x_1*a_{0, 2},
     x_2^2-x_0*x_4+x_5*a_{1, 5}, x_1*x_4-x_0*x_5, x_1*x_5-x_0*x_6+x_5*a_{0, 2}+x_0*a_{1, 5}^2,
     x_2*x_4-x_0*x_6+x_0*a_{1, 5}^2, x_2*x_5-x_1*x_6+x_1*a_{1, 5}^2, x_4^2-x_2*x_6-x_0*x_1*a_{1, 5},
     x_0^3-x_2*x_6+x_0*a_{0, 2}*a_{1, 5}, x_0^2*x_1-x_4*x_5+x_0*x_2*a_{1, 5},
     x_5^2-x_4*x_6+x_0*x_1*a_{0, 2}+x_2*a_{0, 2}*a_{1, 5}+x_4*a_{1, 5}^2,
     x_0^2*x_2-x_4*x_6+x_1*x_2*a_{1, 5}+x_2*a_{0, 2}*a_{1, 5}+x_4*a_{1, 5}^2,
     x_0*x_1*x_2-x_5*x_6+x_0*x_4*a_{1, 5}, x_0^2*x_4-x_6^2+x_4*a_{0, 2}*a_{1, 5}+x_6*a_{1,
     5}^2}},ideal()), ({8, 9, 10, 11, 13, 15},matrix {{x_1^2-x_0*x_2+x_1*a_{0, 2}, x_1*x_2-x_0*x_3,
     x_2^2-x_1*x_3-x_3*a_{0, 2}, x_2*x_3-x_0*x_5, x_3^2-x_1*x_5, x_2*x_5-x_0*x_7+x_2*a_{5, 3},
     x_3*x_5-x_1*x_7+x_3*a_{5, 3}, x_0^3-x_1*x_7-x_7*a_{0, 2}, x_0^2*x_1-x_2*x_7,
     x_5^2-x_3*x_7+x_5*a_{5, 3}, x_0^2*x_2-x_3*x_7-x_0*x_1*a_{0, 2}, x_0*x_1*x_3-x_5*x_7,
     x_0*x_1*x_5-x_7^2+x_0*x_1*a_{5, 3}}},ideal()), ({7, 9, 10, 11, 15},matrix
     {{x_2^2-x_0*x_4+x_0*a_{0, 1}+x_2*a_{0, 2}, x_3^2-x_2*x_4+x_3*a_{1, 3}-x_4*a_{0, 2},
     x_0^3-x_3*x_4+x_3*a_{0, 1}, x_4^2-x_0*x_1-x_4*a_{0, 1}, x_0^2*x_3-x_2*x_1+x_0^2*a_{1,
     3}-x_1*a_{0, 2}, x_0^2*x_4-x_3*x_1, x_0*x_2*x_3-x_4*x_1+x_1*a_{0, 1}+x_0*x_2*a_{1, 3},
     x_2*x_3*x_4-x_1^2+x_2*x_4*a_{1, 3}}},ideal()), ({7, 9, 10, 11, 15},matrix
     {{x_2^2-x_0*x_4+x_0*a_{0, 1}+x_2*a_{0, 2}, x_3^2-x_2*x_4+x_2*a_{0, 1}+x_3*a_{1, 3},
     x_0^3-x_3*x_4-x_4*a_{1, 3}, x_4^2-x_0*x_1-x_4*a_{0, 1}, x_0^2*x_3-x_2*x_1,
     x_0^2*x_4-x_3*x_1-x_0^2*a_{0, 1}-x_1*a_{1, 3}, x_0*x_2*x_3-x_4*x_1+x_1*a_{0, 1}+x_0*x_3*a_{0, 2},
     x_2*x_3*x_4-x_1^2+x_3*x_4*a_{0, 2}}},ideal()), ({7, 8, 10, 12},matrix {{x_3^2-x_1*x_5,
     x_0^2*x_1-x_3*x_5+x_1*a_{1, 2}, x_0^2*x_3-x_5^2+x_3*a_{1, 2}, x_1^3-x_5^2+x_1*a_{3, 2}+x_3*a_{1,
     2}, x_1^2*x_3-x_0^2*x_5+x_3*a_{3, 2}, x_0^4-x_1^2*x_5-x_5*a_{3, 2}+x_0^2*a_{1, 2}}},ideal()),
     ({7, 8, 9, 13, 19},matrix {{x_1^2-x_0*x_2, x_0^3-x_1*x_6, x_0^2*x_1-x_2*x_6, x_6^2-x_0*x_5,
     x_1*x_2^2-x_0*x_5+x_0*a_{4, 1}, x_0^2*x_6-x_1*x_5, x_2^3-x_1*x_5+x_1*a_{4, 1},
     x_0*x_1*x_6-x_2*x_5, x_0^2*x_2^2-x_6*x_5+x_6*a_{4, 1}, x_0*x_2^2*x_6-x_5^2+x_5*a_{4,
     1}}},ideal()), ({7, 8, 9, 13, 19},matrix {{x_1^2-x_0*x_2, x_0^3-x_1*x_6, x_0^2*x_1-x_2*x_6,
     x_6^2-x_0*x_5+x_0*a_{3, 1}, x_1*x_2^2-x_0*x_5, x_0^2*x_6-x_1*x_5+x_1*a_{3, 1}, x_2^3-x_1*x_5,
     x_0*x_1*x_6-x_2*x_5+x_2*a_{3, 1}, x_0^2*x_2^2-x_6*x_5, x_0*x_2^2*x_6-x_5^2+x_5*a_{3,
     1}}},ideal()), ({7, 9, 10, 12, 13},matrix {{x_2*x_3-x_0*x_5, x_3^2-x_0*x_6+x_0*a_{1, 1},
     x_0^3-x_2*x_5+x_0*a_{2, 1}, x_3*x_5-x_2*x_6+x_2*a_{1, 1}, x_0^2*x_2-x_3*x_6,
     x_0^2*x_3-x_5^2+x_3*a_{2, 1}, x_0*x_2^2-x_5*x_6, x_0^2*x_5-x_6^2+x_6*a_{1, 1},
     x_2^3-x_0^2*x_6-x_6*a_{2, 1}}},ideal()), ({7, 8, 11, 12, 13},matrix {{x_1*x_4-x_0*x_5,
     x_1*x_5-x_0*x_6, x_0^3-x_1*x_6+x_1*a_{2, 2}, x_0^2*x_1-x_4^2+x_4*a_{3, 3},
     x_0*x_1^2-x_4*x_5+x_5*a_{3, 3}, x_5^2-x_4*x_6, x_1^3-x_4*x_6+x_6*a_{3, 3},
     x_0^2*x_4-x_5*x_6+x_5*a_{2, 2}, x_0^2*x_5-x_6^2+x_6*a_{2, 2}}},ideal()), ({7, 9, 11, 12, 13,
     15},matrix {{x_2^2-x_0*x_4, x_2*x_4-x_0*x_6, x_0^3-x_2*x_5+x_0*a_{2, 1}+x_2*a_{2, 2},
     x_2*x_6-x_0*x_1+x_0*a_{3, 1}+x_2*a_{3, 2}, x_4^2-x_0*x_1+x_0*a_{3, 1}+x_2*a_{3, 2},
     x_0^2*x_2-x_4*x_5+x_2*a_{2, 1}+x_4*a_{2, 2}, x_4*x_6-x_2*x_1+x_2*a_{3, 1}+x_4*a_{3, 2},
     x_5^2-x_2*x_1-x_4*a_{3, 2}-x_5*a_{2, 2}, x_0^2*x_4-x_5*x_6+x_4*a_{2, 1}+x_6*a_{2, 2},
     x_6^2-x_4*x_1+x_4*a_{3, 1}+x_6*a_{3, 2}, x_0^2*x_5-x_4*x_1+x_5*a_{2, 1}-x_6*a_{3, 2},
     x_0^2*x_6-x_5*x_1+x_5*a_{3, 1}+x_6*a_{2, 1}+x_0^2*a_{3, 2}+x_1*a_{2, 2},
     x_0*x_2*x_5-x_6*x_1+x_0^2*a_{2, 1}-x_1*a_{3, 2}, x_0*x_4*x_5-x_1^2+x_1*a_{3, 1}+x_0*x_2*a_{2,
     1}}},ideal(a_{3, 2}^2+a_{2, 1}*a_{2, 2},a_{2, 1}*a_{3, 2}-a_{3, 1}*a_{2, 2},a_{2, 1}^2+a_{3,
     1}*a_{3, 2})), ({7, 9, 11, 12, 13, 15},matrix {{x_2^2-x_0*x_4, x_2*x_4-x_0*x_6+x_0*a_{1, 1},
     x_0^3-x_2*x_5+x_0*a_{2, 1}, x_2*x_6-x_0*x_1+x_0*a_{3, 1}, x_4^2-x_0*x_1+x_0*a_{3, 1}+x_2*a_{1,
     1}, x_0^2*x_2-x_4*x_5+x_2*a_{2, 1}, x_4*x_6-x_2*x_1+x_2*a_{3, 1}, x_5^2-x_2*x_1-x_4*a_{1,
     1}+x_5*a_{7, 4}, x_0^2*x_4-x_5*x_6+x_4*a_{2, 1}+x_5*a_{1, 1}, x_6^2-x_4*x_1+x_4*a_{3,
     1}-x_6*a_{1, 1}, x_0^2*x_5-x_4*x_1+x_5*a_{2, 1}-x_6*a_{1, 1}+x_0^2*a_{7, 4},
     x_0^2*x_6-x_5*x_1+x_5*a_{3, 1}+x_6*a_{2, 1}, x_0*x_2*x_5-x_6*x_1+x_0^2*a_{2, 1}+x_0*x_2*a_{7, 4},
     x_0*x_4*x_5-x_1^2+x_1*a_{3, 1}+x_0*x_2*a_{2, 1}+x_0*x_4*a_{7, 4}}},ideal(a_{1, 1}^2+a_{2,
     1}*a_{7, 4},a_{2, 1}^2+a_{3, 1}*a_{1, 1})), ({6, 8, 10, 15, 17, 19},matrix {{x_2^2-x_0*x_4,
     x_0^3-x_2*x_4+x_0*a_{1, 1}, x_0^2*x_2-x_4^2+x_2*a_{1, 1}, x_2*x_3-x_0*x_5,
     x_2*x_5-x_0*x_1+x_0*a_{4, 1}, x_4*x_3-x_0*x_1+x_0*a_{4, 1}, x_4*x_5-x_2*x_1+x_2*a_{4, 1},
     x_0^2*x_3-x_2*x_1+x_2*a_{4, 1}+x_3*a_{1, 1}, x_0^2*x_5-x_4*x_1+x_4*a_{4, 1}+x_5*a_{1, 1},
     x_4^3-x_3^2+x_0*x_4*a_{9, 7}-x_0*a_{1, 1}^2, x_0^2*x_4^2-x_3*x_5+x_2*x_4*a_{9, 7}+x_4^2*a_{1,
     1}-x_2*a_{1, 1}^2, x_5^2-x_3*x_1+x_3*a_{4, 1}, x_0*x_2*x_4^2-x_3*x_1+x_3*a_{4, 1}+x_4^2*a_{9,
     7}+x_0^2*x_4*a_{1, 1}, x_0*x_3^2-x_5*x_1+x_5*a_{4, 1}+x_0*x_2*x_4*a_{1, 1}+x_4*a_{9, 7}*a_{1,
     1}+x_0^2*a_{1, 1}^2, x_0*x_3*x_5-x_1^2+2*x_1*a_{4, 1}+x_0*x_4^2*a_{1, 1}+x_0^2*a_{9, 7}*a_{1,
     1}+x_0*x_2*a_{1, 1}^2}},ideal(a_{4, 1}^2-a_{9, 7}*a_{1, 1}^2)), ({6, 9, 10, 13, 17},matrix
     {{x_0^3-x_3^2+x_3*a_{0, 2}, x_3*x_4-x_0*x_1+x_0*a_{1, 1}-x_4*a_{0, 2},
     x_0^2*x_4-x_3*x_1+x_3*a_{1, 1}, x_4*x_1-x_0*x_5+x_0*a_{3, 1}-x_4*a_{1, 1},
     x_1^2-x_3*x_5+x_3*a_{3, 1}-2*x_1*a_{1, 1}+x_5*a_{0, 2}, x_0*x_4^2-x_3*x_5+x_3*a_{3, 1},
     x_3^3-x_4*x_5+x_0*a_{6, 1}+x_4*a_{6, 3}-x_3^2*a_{0, 2}, x_4^3-x_1*x_5+x_1*a_{3, 1}+x_5*a_{1,
     1}-x_0^2*x_3*a_{0, 2}, x_0^2*x_3^2-x_1*x_5+x_3*a_{6, 1}+x_1*a_{6, 3}+x_5*a_{1, 1}-x_0^2*x_3*a_{0,
     2}, x_0^2*x_3*x_1-x_5^2+x_1*a_{6, 1}+x_5*a_{6, 3}+x_5*a_{3, 1}-x_0^2*x_3*a_{1, 1}}},ideal(a_{6,
     3}*a_{0, 2}-a_{3, 1}*a_{0, 2},a_{1, 1}^2-a_{3, 1}*a_{0, 2},a_{3, 1}*a_{1, 1}+a_{6, 1}*a_{0,
     2},a_{6, 3}*a_{1, 1}+a_{6, 1}*a_{0, 2},a_{6, 3}*a_{3, 1}+a_{6, 1}*a_{1, 1})), ({6, 9, 11, 13,
     14},matrix {{x_0^3-x_3^2+x_3*a_{0, 2}, x_3*x_5-x_0*x_2-x_5*a_{0, 2}, x_5^2-x_3*x_1,
     x_0^2*x_5-x_3*x_2, x_0*x_3^2-x_5*x_1+x_5*a_{4, 3}, x_0^2*x_1-x_5*x_2, x_1^2-x_0^2*x_2-x_1*a_{4,
     3}-x_0*x_5*a_{0, 2}, x_3^3-x_1*x_2+x_2*a_{4, 3}-x_3^2*a_{0, 2}, x_0*x_3*x_1-x_2^2-x_0*x_1*a_{0,
     2}}},ideal()), ({6, 9, 11, 13, 14},matrix {{x_0^3-x_3^2+x_3*a_{0, 2}, x_3*x_5-x_0*x_2,
     x_5^2-x_3*x_1+x_1*a_{0, 2}, x_0^2*x_5-x_3*x_2+x_2*a_{0, 2}, x_0*x_3^2-x_5*x_1+x_5*a_{4,
     3}-x_0*x_3*a_{0, 2}, x_0^2*x_1-x_5*x_2, x_1^2-x_0^2*x_2-x_1*a_{4, 3}, x_3^3-x_1*x_2+x_2*a_{4,
     3}-x_3^2*a_{0, 2}, x_0*x_3*x_1-x_2^2}},ideal()), ({6, 7, 11, 16},matrix {{x_0^3-x_1*x_5,
     x_5^2-x_0*x_4, x_0^2*x_5-x_1*x_4, x_0*x_1^3-x_5*x_4+x_0*a_{3, 1}, x_1^4-x_0^2*x_4+x_1*a_{3, 1},
     x_1^3*x_5-x_4^2+x_5*a_{3, 1}}},ideal()), ({6, 8, 11, 13},matrix {{x_2*x_5-x_0*x_1,
     x_0*x_2^2-x_5^2+x_0*a_{1, 1}, x_2^3-x_5*x_1+x_2*a_{1, 1}, x_0^4-x_5*x_1+x_0*a_{3, 1},
     x_0^3*x_2-x_1^2+x_2*a_{3, 1}, x_0^3*x_5-x_2^2*x_1+x_5*a_{3, 1}-x_1*a_{1, 1}}},ideal()), ({7, 8,
     9, 12},matrix {{x_1^2-x_0*x_2, x_0^3-x_2*x_5+x_5*a_{1, 4}, x_0*x_1*x_2-x_5^2+x_5*a_{2,
     4}+x_0*x_1*a_{1, 4}, x_1*x_2^2-x_0^2*x_5+x_0^2*a_{2, 4}-x_1*a_{1, 4}^2,
     x_2^3-x_0*x_1*x_5+x_0*x_1*a_{2, 4}-x_2*a_{1, 4}^2}},ideal()), ({7, 8, 9, 12},matrix
     {{x_1^2-x_0*x_2+x_0*a_{0, 1}, x_0^3-x_2*x_5+x_2*a_{1, 3}, x_0*x_1*x_2-x_5^2+x_5*a_{1,
     3}+x_0*x_1*a_{0, 1}, x_1*x_2^2-x_0^2*x_5+x_1*x_2*a_{0, 1}, x_2^3-x_0*x_1*x_5-x_2*a_{0,
     1}^2}},ideal()), ({8, 9, 10, 11, 13, 15},matrix {{x_1^2-x_0*x_2+x_0*a_{0, 1}, x_1*x_2-x_0*x_3,
     x_2^2-x_1*x_3-x_2*a_{0, 1}, x_2*x_3-x_0*x_5, x_3^2-x_1*x_5, x_2*x_5-x_0*x_7+x_0*a_{5, 1},
     x_3*x_5-x_1*x_7+x_1*a_{5, 1}, x_0^3-x_1*x_7, x_0^2*x_1-x_2*x_7+x_7*a_{0, 1},
     x_5^2-x_3*x_7+x_3*a_{5, 1}, x_0^2*x_2-x_3*x_7, x_0*x_1*x_3-x_5*x_7+x_0*x_2*a_{0, 1},
     x_0*x_1*x_5-x_7^2+x_7*a_{5, 1}+x_1*x_3*a_{0, 1}+x_2*a_{0, 1}^2}},ideal()), ({8, 9, 10, 12, 13,
     14},matrix {{x_1^2-x_0*x_2+x_1*a_{0, 2}, x_2^2-x_0*x_4+x_5*a_{1, 5}, x_1*x_4-x_0*x_5,
     x_1*x_5-x_0*x_6+x_5*a_{0, 2}, x_2*x_4-x_0*x_6, x_2*x_5-x_1*x_6, x_4^2-x_2*x_6-x_0*x_1*a_{1,
     5}-x_2*a_{1, 5}^2, x_0^3-x_2*x_6+x_0*a_{0, 2}*a_{1, 5}-x_2*a_{1, 5}^2,
     x_0^2*x_1-x_4*x_5+x_0*x_2*a_{1, 5}, x_5^2-x_4*x_6+x_0*x_1*a_{0, 2}+x_2*a_{0, 2}*a_{1, 5},
     x_0^2*x_2-x_4*x_6+x_1*x_2*a_{1, 5}+x_2*a_{0, 2}*a_{1, 5}, x_0*x_1*x_2-x_5*x_6+x_0*x_4*a_{1,
     5}-x_5*a_{1, 5}^2, x_0^2*x_4-x_6^2+x_4*a_{0, 2}*a_{1, 5}-x_6*a_{1, 5}^2}},ideal()), ({8, 9, 10,
     11, 13, 14},matrix {{x_1^2-x_0*x_2+x_1*a_{0, 2}, x_1*x_2-x_0*x_3, x_2^2-x_1*x_3-x_3*a_{0, 2},
     x_2*x_3-x_0*x_5+x_2*a_{3, 3}, x_1*x_5-x_0*x_6, x_3^2-x_0*x_6+x_3*a_{3, 3},
     x_2*x_5-x_1*x_6-x_6*a_{0, 2}, x_3*x_5-x_2*x_6, x_0^3-x_2*x_6-x_5*a_{3, 3}+x_0^2*a_{8, 7},
     x_0^2*x_1-x_3*x_6-x_6*a_{3, 3}+x_0*x_1*a_{8, 7}, x_0^2*x_2-x_5^2+x_0*x_2*a_{8, 7},
     x_0^2*x_3-x_5*x_6+x_0*x_3*a_{8, 7}, x_0*x_1*x_3-x_6^2+x_1*x_3*a_{8, 7}}},ideal()), ({8, 9, 10,
     11, 13, 14},matrix {{x_1^2-x_0*x_2+x_1*a_{0, 2}+x_2*a_{0, 3}, x_1*x_2-x_0*x_3+x_3*a_{0, 3},
     x_2^2-x_1*x_3-x_3*a_{0, 2}, x_2*x_3-x_0*x_5+x_2*a_{3, 3}, x_1*x_5-x_0*x_6+x_6*a_{0, 3},
     x_3^2-x_0*x_6+x_3*a_{3, 3}, x_2*x_5-x_1*x_6-x_6*a_{0, 2}, x_3*x_5-x_2*x_6,
     x_0^3-x_2*x_6-x_5*a_{3, 3}-x_0^2*a_{0, 3}, x_0^2*x_1-x_3*x_6-x_6*a_{3, 3},
     x_0^2*x_2-x_5^2-x_0*x_2*a_{0, 3}, x_0^2*x_3-x_5*x_6-x_0*x_3*a_{0, 3},
     x_0*x_1*x_3-x_6^2}},ideal())}

LLFamiliesWithRelations=select(LLMinFamilies,D->(D_2 !=0))
#oo
netList flatten apply(LLFamiliesWithRelations,D->(cD2=decompose D_2; apply(cD2,c->(
	    D_0,#cD2,numgens c,#support D_2,#support D_1,#support c+#D_0,c)))
)
-*
      +-----------------------------------------------------------------------------------------------------------------------------------------------------+
o22 = |({8, 9, 10, 11, 12, 13}, 3, 2, 4, 10, 8, ideal (a      , a      ))                                                                                   |
      |                                                 {2, 1}   {4, 1}                                                                                     |
      +-----------------------------------------------------------------------------------------------------------------------------------------------------+
      |({8, 9, 10, 11, 12, 13}, 3, 2, 4, 10, 8, ideal (a      , a       ))                                                                                  |
      |                                                 {2, 1}   {10, 4}                                                                                    |
      +-----------------------------------------------------------------------------------------------------------------------------------------------------+
      |                                                                      2                                                                              |
      |({8, 9, 10, 11, 12, 13}, 3, 2, 4, 10, 10, ideal (a        - a      , a       + a       a      ))                                                     |
      |                                                  {10, 4}    {4, 1}   {4, 1}    {10, 3} {2, 1}                                                       |
      +-----------------------------------------------------------------------------------------------------------------------------------------------------+
      |                                           2                                                                                                         |
      |({6, 8, 10, 13, 15}, 1, 1, 3, 8, 8, ideal(a       - a      a      ))                                                                                 |
      |                                           {3, 1}    {6, 2} {1, 1}                                                                                   |
      +-----------------------------------------------------------------------------------------------------------------------------------------------------+
      |({6, 8, 10, 13, 17}, 2, 2, 5, 11, 7, ideal (a      , a      ))                                                                                       |
      |                                             {0, 1}   {3, 3}                                                                                         |
      +-----------------------------------------------------------------------------------------------------------------------------------------------------+
      |                                                                                     2                                                               |
      |({6, 8, 10, 13, 17}, 2, 3, 5, 11, 10, ideal (a       + a      , a       + 2a      , a       + a      a      ))                                       |
      |                                              {5, 7}    {0, 1}   {5, 5}     {3, 3}   {3, 3}    {5, 3} {0, 1}                                         |
      +-----------------------------------------------------------------------------------------------------------------------------------------------------+
      |                                                  2                                                          2                                       |
      |({7, 9, 11, 12, 13, 15}, 1, 3, 4, 10, 10, ideal (a       + a      a      , a      a       - a      a      , a       + a      a      ))               |
      |                                                  {3, 2}    {2, 1} {2, 2}   {2, 1} {3, 2}    {3, 1} {2, 2}   {2, 1}    {3, 1} {3, 2}                 |
      +-----------------------------------------------------------------------------------------------------------------------------------------------------+
      |({7, 9, 11, 12, 13, 15}, 2, 2, 4, 10, 8, ideal (a      , a      ))                                                                                   |
      |                                                 {1, 1}   {2, 1}                                                                                     |
      +-----------------------------------------------------------------------------------------------------------------------------------------------------+
      |                                                  2                                                          2                                       |
      |({7, 9, 11, 12, 13, 15}, 2, 3, 4, 10, 10, ideal (a       + a      a      , a      a       - a      a      , a       + a      a      ))               |
      |                                                  {1, 1}    {2, 1} {7, 4}   {2, 1} {1, 1}    {3, 1} {7, 4}   {2, 1}    {3, 1} {1, 1}                 |
      +-----------------------------------------------------------------------------------------------------------------------------------------------------+
      |                                               2                2                                                                                    |
      |({6, 8, 10, 15, 17, 19}, 1, 1, 3, 9, 9, ideal(a       - a      a      ))                                                                             |
      |                                               {4, 1}    {9, 7} {1, 1}                                                                               |
      +-----------------------------------------------------------------------------------------------------------------------------------------------------+
      |({6, 9, 10, 13, 17}, 3, 3, 5, 10, 8, ideal (a      , a      , a      ))                                                                              |
      |                                             {0, 2}   {1, 1}   {3, 1}                                                                                |
      +-----------------------------------------------------------------------------------------------------------------------------------------------------+
      |({6, 9, 10, 13, 17}, 3, 3, 5, 10, 8, ideal (a      , a      , a      ))                                                                              |
      |                                             {0, 2}   {1, 1}   {6, 3}                                                                                |
      +-----------------------------------------------------------------------------------------------------------------------------------------------------+
      |                                                                 2                                                          2                        |
      |({6, 9, 10, 13, 17}, 3, 4, 5, 10, 10, ideal (a       - a      , a       - a      a      , a      a       + a      a      , a       + a      a      ))|
      |                                              {6, 3}    {3, 1}   {1, 1}    {3, 1} {0, 2}   {3, 1} {1, 1}    {6, 1} {0, 2}   {3, 1}    {6, 1} {1, 1}  |
      +-----------------------------------------------------------------------------------------------------------------------------------------------------+



*-
restart
needsPackage "AIWeierstrass"
g=10
LL=select(findSemigroups g,L->not knownExample L and min L >5);
#LL
LL
--elapsedTime LLb=produceBounds(LL,"bounds10n");
--LLb=continueComputation(produceBounds,LL,"bounds10n")
LLb1=unique getFromDisk "bounds10n"

#LLb1
tally apply(LLb1,D->D_1)
pos=positions(LLb1,D->D_1<3)
netList apply(LLb1_pos,Lb->(L,degreeMatrices Lb_0))
-- reorder LLb1 to make difficul
LLb1r=LLb1_{0..5,7..15,17..39,41..76,6,40,16}
#LLb1r==#LL
LLb1r_18
LLb1_20

elapsedTime LLR=produceRangesFromBounds(LLb1r,"ranges10r");
LLRa= getFromDisk "ranges10r"
#LLRa
(last LLRa)
LLb1r_6,degreeMatrices (LLb1r_6)_0

elapsedTime LLR=continueComputation(produceRangesFromBounds,LLb1r,"ranges10r")

LLb1=unique getFromDisk "bounds10n"
LLb1r=LLb1_{0..5,7..15,17..19,21..39,41..76,6,40,16,20}
#LLb1
LLRa= getFromDisk "ranges10r"
#LLRa
LLb1_21

elapsedTime LLR=continueComputation(produceRangesFromBounds,LLb1r,"ranges10r")

restart
needsPackage "AIWeierstrass"
{7, 8, 11, 17, 20}
-- continue from here
LLb1=unique getFromDisk "bounds10n"
#LLb1
LLRa= getFromDisk "ranges10r"
#LLRa
tally apply(LLRa,Lr->(max Lr_1-min Lr_1))
tally apply(LLRa,Lr->(Lr_1_0,#Lr_1))
    LLb1_6
tally apply(LLb1,Lb-> Lb_1)
pos=position(LLb1,Lb->Lb_0=={7,8,11,17,20})
--LLb1_49 --might be easy
netList apply(LLb1_{43,20,40,16},Lb->(ms=degreeMatrices Lb_0;
    (Lb,transpose ms_0,ms_1, last ms)))
LLb1r=LLb1_{0..5,7..15,17..19,21..28,30..39,41,42,44..76,6,29,43,20,40,16}
#LLb1r,#LLRa
elapsedTime LLR=continueComputation(produceRangesFromBounds,LLb1r,"ranges10r")


LLR=getFromDisk "ranges10r"
#LLR==73
last LLR
elapsedTime LLSR=produceShrinkedRangesFromRanges(LLR,"shrinkedRanges10r");
LLSR= getFromDisk "shrinkedRanges10r"
select(LL
#LLSR==72
netList apply(#LLSR,i->(LR=LLSR_i;(i,LR_0,#LR_1,min LR_1,max LR_1)))
tally apply(LLSR,LR->#LR_1)
LLSRs=sort(LLSR,LR->#LR_1)

elapsedTime LLMinLists=flatten produceMinListsFromRanges(LLSRs,2,"minLists10r");
restart
needsPackage "AIWeierstrass"
ls()

LLMinLists=getFromDisk "minLists10r";
#LLMinLists
last LLMinLists
tally apply(LLMinLists,Lp->#Lp_1)
LLSR= getFromDisk "shrinkedRanges10r";
#LLSR==72
LL72=apply(LLSR,LR->LR_0)
tally apply(LLSR,LR->#LR_1)
LLSRs=sort(LLSR,LR->#LR_1);


    elapsedTime LLMinLists=flatten produceMinListsFromRanges(LLSRs,2,"minLists10ra");
-- 137882s elapsed for 70
 -- 19769.5s elapsed
19769.5/60/60
137882/60/60+0.0
LLMinLists10a70=getFromDisk "minLists10ra";
#LLMinLists10a70

toString LLMinLists10a70
LL70=unique apply(flatten LLMinLists10a70,LP->LP_0)
#LL70
LL7=select(LL,L->not member(L,LL70))
    toString LLMinLists
elapsedTime LLMinFamilies=produceMinimalFamiliesFromMinLists(LLMinLists,"minFams10n");
--------- for tex file Example 3.2
restart
needsPackage "AIWeierstrass"
kk=ZZ/nextPrime 10^4
c=7
L={6,9,9+c,12+c}
I=semigroupIdeal L
I_4,I_5
S=kk[x_3,y,z,x_0,
    Degrees=>apply((gens ring I)_{1,2,3,0},m->degree m)]
fI=res sub(I,matrix{{x_0,x_3,y,z}})
fI.dd_1_{4,5}%fI.dd_1_{0..3}
I=ideal(fI.dd_1_{0..3}|(fI.dd_1_{4,5}%fI.dd_1_{0..3}))
fI=res I
transpose fI.dd_1
netList apply({1,2,4,5,7,8,10,11},c->(
	L={6,9,9+c,12+c};
	I=semigroupIdeal L;
	S=kk[x_3,y,z,x_0,Degrees=>apply((gens ring I)_{1,2,3,0},m->degree m)];
	fI=res sub(I,matrix{{x_0,x_3,y,z}});
        I=ideal(fI.dd_1_{0..3}|(fI.dd_1_{4,5}%fI.dd_1_{0..3}));
	fI=res I;
	(c,c%6,transpose (fI.dd_1)_{0..3})))
netList apply({1,2,4,5,7,8,10,11},c->(
	L={6,9,9+c,12+c};
	I=semigroupIdeal L;
	S=kk[x_3,y,z,x_0,Degrees=>apply((gens ring I)_{1,2,3,0},m->degree m)];
	fI=res sub(I,matrix{{x_0,x_3,y,z}});
        I=ideal(fI.dd_1_{0..3}|(fI.dd_1_{4,5}%fI.dd_1_{0..3}));
	fI=res I;
	(c,c%6,transpose (fI.dd_1)_{4,5})))

--------- for tex file Example 3.3
restart
needsPackage "AIWeierstrass"
L={7,15,23,39}
degreeMatrices L
I=semigroupIdeal L
S=ring I
res I
--elapsedTime testWeierstrass(L,6)
range=apply(11,i->7*(i+1))
elapsedTime testWeierstrassRange(L,range)==-1 -- 1.0591s elapsed
elapsedTime sRange=shrinkRange(L,range) -- 46.4539s elapsed
sRange={7,63,70,77}
elapsedTime posList=minimalPositionLists(L,sRange,2,Verbose=>true)
finList={6,29,30,68,78}
displayMinimalFamilies {(L,finList)}
(J,family,runfolding,J1)=showRestrictedFamily(L,finList)
support family
SQQ=QQ[gens S,Degrees=>degrees S] 
fiber=ideal sub(family,vars SQQ|matrix{{1,1}})
dim singularLocus(SQQ/fiber)
SQQt=QQ[(gens S)_{1,2,3,0}|{t},Degrees=>((degrees SQQ)_{1,2,3,0}|{1})]
fibt=homogenize(sub(fiber,SQQt),t)
betti res fibt== betti res I --=>flatness
degrees ring family 
---------
tex ideal gens fibt
tex transpose gens fibt
 ffibt=res fibt
ffibt.dd_2,ffibt.dd_3
--- multiplcities of degree special 1683
LL1683s=value get "LLh45-15-30-15s";
first LL1683s
netList apply(toList(6..45),m->(m,min apply(select(LL1683s,Lh->Lh_0_0==m),Lh->Lh_1)))
-- looks like every multiplicity >=6 occurs
primes={7,11,13,17,19,23,29,31,37,41,43}
netList apply(primes,m->(m,sort apply(select(LL1683s,Lh->Lh_0_0==m),Lh->Lh_1)))
tally apply(select(LL1683s,Lh->(Lh_1)%3==0),Lh->((Lh_3_0,Lh_3_2)))


--------- for tex file Example 3.4
restart
needsPackage "AIWeierstrass"
L={12,15,18,26,32}
degreeMatrices L
I=semigroupIdeal L
S=ring I
fI=res I
fI.dd_2
J=ideal (fI.dd_1)_{0..4}
fJ=res J
range=apply(7,i->(i+1)*12)
elapsedTime testWeierstrassRange(L,range) -- 3.32744s elapsed
range=apply(21,i->(i+1)*4)
elapsedTime testWeierstrassRange(L,range) -- 5.09084s elapsed
elapsedTime testWeierstrass(L,8)  -- 35.407s elapsed
elapsedTime testWeierstrass(L,0)
range=apply(42,i->(i+1)*2)
elapsedTime testWeierstrassRange(L,range)

-- Komeda's argument
restart
needsPackage "AIWeierstrass"
l=2
n=8*l-1
m=4
Ltilde={8,12,8*l+2,8*l+6,n,n+4}
gtilde =#(G=gaps Ltilde)
apply(3,i->(Gi=G;Gi=sums(Gi,G);(2*i+3)*(gtilde-1)-#Gi))
L={4,6,4*l+1,4*l+3}
c=(apery L)#"conductor"
n>=2*c-1
n,2*m-1
g=#gaps L
gaps L
I=semigroupIdeal L
S=ring I
fI=res I
degreeMatrices L
degreeMatrices Ltilde
Itilde=semigroupIdeal Ltilde
R=ring Itilde
fItilde=res Itilde
si=6
n+2*(si-m)==n+4

ramific=2*gtilde-2-2*(2*g-2)

2*g-2-(4*l+3-4-1)
(4*l+1-4,1)
(6-4,1)
smax=4*l+3
si=6
smax-m-1
smax-m==7
2*g-2-(smax-m-1)
gaps L
2*g-2-6
--h^0(K-6p)=2+h^0(6p)+1-g=2+3+1-5=1
--0=h^0(K-6p-p1)=h^0(6p+p1)+2*g-2-7+1-g=h^0(6p+p1)+g-1-7
-- => h^0(6p+p1)=3 ,h^0(K-7p-p1)=0 => h^0(7p+p1)=8+1-5=4=3+1=h^0(6p)+1
-- => h^0(7p+p1)=8+1-5=4=3+1=h^0(6p+p1)+1
-- => want h^0((si-m)p+p1)=h^0((si-m-1)p+p1)+1
--         h^0(2p+p1)=h^0(p+p1)+1=2
-- if not then h^0((si-m)p+p1)=h^0((si-m-1)p+p1)
(si-m,1) 
(n+1)/2
--D=8p-p1
-- degree (2D-p)=2*7-1=13>2*g+2
13>2*g+2
tildeK=
not member(n+2*(si-m),gaps Ltilde)
--=> h^0(tildeK-(n+2*(si-m))tildep) = h^0(tildeK-(n+2*(si-m)-1)tildep)
-- h^0((si-m)p+p1)=h^0(s
restart
needsPackage "AIWeierstrass"
F = res semigroupIdeal{6,9,13,16}
F.dd

pseudoFrobenius = L -> (
    s = sum L;
    fL = res semigroupIdeal L;
    D = flatten degrees (fL_(length L-1));
    apply(D, d-> d-s)
    )
g = 14
pseudoFrobenius {6,9,g,g+3}

semigroup L
--PF {5,6,7} = 8,9
---
restart
needsPackage "AIWeierstrass"
L = {3,4,5}
I = semigroupIdeal L
betti (F = res I)
syzFormat F
degreeMatrices F
F.dd

L = {6,9,13,16}
I = semigroupIdeal L
F = res I
syzFormat F
degreeMatrices F
I_*
I_*_{0..3}
J = ideal(I_*_{0..3})
syzFormat J
(res J).dd_2
buchweitz 0
