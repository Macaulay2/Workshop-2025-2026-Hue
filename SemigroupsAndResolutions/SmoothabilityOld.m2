newPackage(
          "SmoothabilityOld",
          Version => "0.1",
          Date => "",
          Headline => "Routines from NumericalSemigroups",
          Authors => {{ Name => "", Email => "", HomePage => ""}},
          Keywords => {""},
          AuxiliaryFiles => false,
          DebuggingMode => true,
          PackageExports => {
	"FourierMotzkin",
	"Normaliz",
	"IntegralClosure",
	"FastMinors",
	"RandomPoints",
	"sgrps1"
--	"NumericalSemigroups"
	},
    Keywords => {"Commutative Algebra", "Algebraic Geometry", "Combinatorics"}
)
      export {
    "def1", --TEST created -- degrees of first order deformations, or the generic first-order deformation itself.
    "findPoint", --done
    "heuristicSmoothness", --done
    "knownExample", --done FOS
    "isARandomFiberSmooth", --done FOS
    "getFlatFamily", --done FOS
    "isWeierstrassSemigroup", -- done FOS
    "nonWeierstrassSemigroups", -- done FOS
    "LabBookProtocol", --done FOS
    "makeUnfolding", -- TEST created
    "flatteningRelations", --TEST created
    "isSmoothableSemigroup", --TEST created
}

      -* Code section *-

def1 = method(Options => {"BaseField" => ZZ/101,"JustDegs" => true})--, "BaseField"})
def1 List := o -> L -> (
 --degrees of first-order deformations or the generic first-order deformation itself.
 B := semigroupRing (L, "BaseField" => o#"BaseField");
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

t2 = method(Options => {"BaseField" => ZZ/101})
t2 List := o -> L -> (
 B := semigroupRing (L, "BaseField" => o#"BaseField");
 I := ideal B;
 S := ring I;
 prune Ext^1(I, S^1/I)
 )
    
findPoint=method(Options => {Verbose => false})
    
findPoint(Ideal) := o -> (c) -> (
    c1 := prune c;  
    R := ring c;
    A1 := vars R % c;
    if c1==0 then return sub(A1,random(R^1,R^(numgens R)));
    if o.Verbose then << "has to solve" <<flush<< endl;
    kk:= coefficientRing R;
    leftOverVars := support c;
    R1:=kk[support c];
    cR1:=sub(c,R1);
    isHomogeneous cR1;
    if o.Verbose then (
    elapsedTime point := sub(matrix randomPoints(cR1,Homogeneous=>false),kk);) else (
                point = sub(matrix randomPoints(cR1,Homogeneous=>false),kk));
    subs1:=apply(#leftOverVars,i->leftOverVars_i => point_(0,i));
    assert(sub(cR1,subs1)==0);
    --ring c === ring A1;
    A2:=sub(sub(A1,subs1),R);
    return sub(A2,random(R^1,R^(numgens R)));
    )
    
restrict = method()
restrict(List, Matrix) := (params, genmat) -> {}
///
L = {7,8,9}
r = .25;n=0;
r = 1;n=0;
(I, J1, family) = getFlatFamily(L,r,n)
trim J1
///

getFlatFamily=method(Options =>
      {Verbose => false,
      "BaseField" => ZZ/10007})

getFlatFamily(List,RR,ZZ) := o -> (L,r,n) -> (
    I := semigroupIdeal(L, "BaseField"=> o#"BaseField");
    if o.Verbose then (
        degsT1:=-def1 L;
	<< "unfolding" <<endl<<flush;
        elapsedTime (A,unfolding):= makeUnfolding I;) else (
	degsT1=-def1 L;
	(A,unfolding)= makeUnfolding I);
    ma:=max degsT1;
    S:=ring I;
    SA:=ring unfolding;
    restrict:=ideal select( gens A, aa->(degree aa)_0<=ma*r+n);
    runfolding:=unfolding%sub(restrict,SA);
    if o.Verbose then (
	 <<"flatteningRelations"<<endl<<flush;
          elapsedTime J:=flatteningRelations(I,A,runfolding);
	  ) else (
	 J=flatteningRelations(I,A,runfolding));
    mA:= max flatten degrees A;
    if o.Verbose then (
	<<"next gb" << endl<<flush;
	elapsedTime gbJ:=forceGB gens gb(J,DegreeLimit=>mA);) else (
	gbJ=forceGB gens gb(J,DegreeLimit=>mA););
	varsAmodJ:=vars A%gbJ;
    J1:=sub(J,varsAmodJ);
    family:=sub(runfolding,sub(vars S,SA)|sub(varsAmodJ,SA));
    if J1==0 then assert (betti syz family==betti syz gens I);
    (I,J1,family))

isWeierstrassSemigroup=method(Options =>
      {Verbose => false,
      "BaseField" => ZZ/10007})

isWeierstrassSemigroup(List,RR) := o -> (L,r) -> (
    if o.Verbose then (elapsedTime degT1:=def1(L);) else degT1=def1(L);
    truncations:=-unique select(degT1,d->d<0);
    I:=semigroupIdeal L;
    S:=ring I;
    (A,unfolding):=makeUnfolding I;
    ma:=max flatten (gens A/degree);
    truncations=select(truncations,d->d<ma*r+1);
    J1:=null; family:= null;
    for t in truncations do ( if o.Verbose then (<<t<<endl<<flush);
	 (I,J1,family)=getFlatFamily(L,0.0,t-1);
                 if isARandomFiberSmooth(I,J1,family,o) then
		 ( break return true));
    return false)
-*
estimateTruncationRatio=method()
estimateTruncationRatio(List) := LL -> (
    I:=null;S:=null;A:=null;unfolding:=null;
    J1:=null; family:= null;ratio:=null;degT1:=null;
    truncations:=null;ma:=null;t:=null;answer:=null;
    ratios:=apply(LL,L -> (
	    <<L <<endl<<flush;
	    elapsedTime degT1=def1(L);
    truncations=-unique select(degT1,d->d<0);
    I=semigroupIdeal L;
    S=ring I;
    (A,unfolding)=makeUnfolding I;    
    ma=max flatten degrees A;
    for t in truncations do (
	elapsedTime (<<t<<endl<<flush;
	elapsedTime (I,J1,family)=getFlatFamily(L,0.0,t-1);
                 --<<(isARandomFiberSmooth(I,J1,family),t) <<flush<< endl;
		 answer= isARandomFiberSmooth(I,J1,family));
                 if answer then
		 ( << t-1<<endl<<flush; ratio=(ma,max truncations,t-1); break ));
	     ratio)
	 );
	 ratios)
*-
///
---- current test ---------
restart
debug loadPackage("NumericalSemigroups",Reload=>true)
L={6, 9, 14, 19, 22}
genus L

apply(LL,L->(I=semigroupIdeal L; (A,unfolding)=makeUnfolding I;
                mA= max flatten degrees A;degT1=-def1 L;(ma,max degT1)))



elapsedTime isWeierstrassSemigroup L



J1==0
J1
SA=ring family
ffam=res ideal family
ffam.dd_4
isSmoothableSemigroup(L,0.2,0)
///

isARandomFiberSmooth=method(Options =>
      {Verbose => false,
      "BaseField" => ZZ/10007})
isARandomFiberSmooth(Ideal,Ideal,Matrix) := o -> (I,J1,family) -> (
    S := ring I;
    A := ring J1;
    fib:=null;answer:= null;
    if J1==0 then (fib = ideal sub(family,vars S|random(S^1,S^(numgens A)));
	answer = heuristicSmoothness(fib);
	if o.Verbose then <<answer <<endl<<flush;
	return answer);   
     kk := coefficientRing A;
     
--decompose here
-*   
     varsJ1:=support J1;
     R1:=kk[varsJ1];  
     elapsedTime J1ungraded:=trim ideal map(R1^1,,gens sub(J1,R1));
     << "in isARandomFiber decomposition, " <<  "(numgens,#support): " << (numgens J1ungraded,#support J1ungraded)<< endl;

     elapsedTime cJ1un:=decompose J1ungraded;
     cJ1:=apply(cJ1un,c->ideal map(A^1,,gens sub(c,matrix{ varsJ1})));
*-
    if o.Verbose then (<<"decompose" <<endl<<flush;
         elapsedTime cJ1:=decompose (J1); -- perhaps moved to a new ring
         <<"number of components: "<< #cJ1 <<endl<<flush;) else (
         cJ1=decompose J1);
    A2:=null;point:=null; 
    dims:=apply(cJ1,c->(
	    A2=findPoint(c);
	    --point=sub(sub(h,A2),coefficientRing A);
	    point=sub(A2,coefficientRing A);
	    assert(
		sub(J1,point)==0);
	    fib=ideal sub(family,vars S|point);
	    ---break return fib;
	    --assert(betti syz gens fib == betti syz gens I);
	    answer = heuristicSmoothness(fib);
	    --  singF=radical ideal gens gb (fib +minors(#mingens L-1,jacobian fib));
	    if answer then -1 else 0
	    --dim singF
	    ));
      if o.Verbose then (
	  << "support c, codim c: " <<apply(cJ1,c->(#support c,codim c)) <<endl<<flush;
	  <<dims <<endl<<flush;);
      return min dims ==-1 )

 
///
LL12d
L=LL12d_2
filterSmoothable(L,0.30,1)

///


  
heuristicSmoothness=method(Options =>
      {Verbose => false,
      "BaseField" => ZZ/10007})
heuristicSmoothness(Ideal) := o -> fib -> (
    --VerifyNonRegular:= null;
    --regularInCodimension(1, (ring fib)/fib, VerifyNonRegular=>true, Verbose=>true) )
    jac := jacobian fib;
    kk:=coefficientRing ring fib;
    R1:=kk[support fib];
    points:= fib;N:=1;
    numberOfSingPoints:=null;dimPoints:=null;
    rad:=null;someMinors:=null;
    while (
	someMinors = chooseGoodMinors(20*N,numgens ring fib-1,jac);
	points = ideal gens gb (points+someMinors);
	dimPoints=dim points;
	if dimPoints>-1 then (
	    rad = radical points;
	    numberOfSingPoints=degree sub(rad,R1););
    dimPoints>-1 and numberOfSingPoints>1 and N<2) do (N=N+1);
    if dimPoints==-1 then return true;
    jacpt:=sub(jac,vars ring fib%rad);
    if numberOfSingPoints==1 then (
	return rank jacpt==codim fib) else (
	if o.Verbose then (
	<<"numberOfSingPoints "<<numberOfSingPoints <<endl<<flush;);
        return false)
	--return dim(rad+minors(codim fib,jacpt))==-1)
    )


knownExample=method()
knownExample(List) := L-> (
    if #L<=3 then return true;--determinantal
    if #L == 4 and type L == 1 then return true;--pfaffian
    --if L is a generalized Arithmeti cProgression L
    --then in some cases the paper of Oneto and Tamone shows smoothness
    g := genus L;
    if ewt L < g or min L <5 then return true else false)

nonWeierstrassSemigroups=method(Options =>
      {Verbose => false,
      "BaseField" => ZZ/10007})
nonWeierstrassSemigroups(ZZ,ZZ) := o -> (m,g) -> (
    LL:= findSemigroups(m,g);
    LLa:=select(LL,L->not knownExample L);
    if o.Verbose then <<(#LL,#LLa) <<endl<<flush;
    r:=0.65;
    while ( LLa=select(LLa,L-> (
		if o.Verbose then (<<L<<endl<<flush;
		 elapsedTime not isSmoothableSemigroup(L,r,0,o)
		 ) else (not isSmoothableSemigroup(L,r,0,o))));
	     #LLa >6 ) do (r=r-0.05;if o.Verbose then (<<#LLa<<endl<<flush;<<endl;));
    LLa=select(LLa,L->(if o.Verbose then (<<L<<endl<<flush;
		elapsedTime not isWeierstrassSemigroup(L,r,o)) else (
		not isWeierstrassSemigroup(L,r,o))));
    if #LLa==0 then (<<(m,g," all semigroups are smoothable")<<flush<<endl);
    LLa)

nonWeierstrassSemigroups(ZZ,ZZ,List) := o -> (m,g,LLdifficult) -> (
    LL:= findSemigroups(m,g);
    LLa:=sort select(LL,L->not knownExample L);
    <<(#LL,#LLa) <<endl<<flush;
    LLa=select(LLa,L->not isMember(L,LLdifficult));
    r:=0.6;
    while ( elapsedTime LLa=select(LLa,L-> (<<L<<endl<<flush;
		 not elapsedTime isSmoothableSemigroup(L,r,0,o)));
	<<#LLa<<endl;<<endl<<flush;
	#LLa >6 ) do (r=r-0.1);
    <<LLa <<endl;
    n:= 0;
    elapsedTime LLa=select(LLa,L->(<<n<< L <<endl<<flush;n=n+1;
		elapsedTime not isWeierstrassSemigroup(L,r,o)));
    --if #LLa==0 then (<<(m,g," all but difficult semigroups are smoothable")<<flush<<endl);
    LLa|LLdifficult)


LabBookProtocol = method()
LabBookProtocol ZZ := String => g ->(

    if g == 7 then print("
    LL7=findSemigroups 7;#LL7
    LL7a=select(LL7,L->not knownExample L);#LL7a
    elapsedTime LL7b=select(LL7a,L->not isSmoothableSemigroup(L,0.25,0))
    LL7b=={} -- => every genus 7 semigroup is Weierstrass
    ");

    if g == 8 then print("
	LL8=findSemigroups 8;#LL8
	LL8a=select(LL8,L->not knownExample L);#LL8a
	elapsedTime LL8b=select(LL8a,L-> not isSmoothableSemigroup(L,0.40,0)) -- 16.7345 seconds elapsed
        LL8b=={{6,8,9,11}}
	elapsedTime LL8c=select(LL8b,L-> not isWeierstrassSemigroup(L,0.15)) --  1.88664 seconds elapsed
        LL8c=={} -- => every genus 8 semigroup is Weierstrass
    ");

    if g == 9 then print("
    LL9=findSemigroups 9;#LL9
    LL9a=select(LL9,L->not knownExample L);#LL9a
    elapsedTime LL9b=select(LL9a,L->(not isSmoothableSemigroup(L,0.5,0)));#LL9b -- 134.401 seconds elapsed
    LL9b
    elapsedTime LL9c=select(LL9b,L->(not isSmoothableSemigroup(L,0.4,0)));  -- 26.7357 seconds elapsed
    LL9c=={} -- => every genus 8 semigroup is Weierstrass
    ");

    if g == 10 then print("
    LL10=findSemigroups 10;#LL10
    LL10a=select(LL10,L->not knownExample L);#LL10a
    elapsedTime LL10b=select(LL10a,L-> elapsedTime not isSmoothableSemigroup(L,0.6,0)); -- 418.486 seconds elapsed
    #LL10b 
    elapsedTime LL10c=select(LL10b,L->(<<L<<endl<<flush;elapsedTime not isSmoothableSemigroup(L,0.5,0))); -- 173.422 seconds elapsed-
    #LL10c 
    elapsedTime LL10d=select(LL10c,L->(<<L<<endl<<flush;elapsedTime not isSmoothableSemigroup(L,0.45,0))); -- 156.571 seconds elapsed
    LL10d
    elapsedTime LL10e=select(LL10d,L->(<<L<<endl<<flush;elapsedTime not isWeierstrassSemigroup(L,0.4)));   -- 197.321 seconds elapsed 
    LL10e=={} -- => every genus 10 semigroup is Weierstrass
    ");

    if g == 11 then print("
    LL11=findSemigroups 11;#LL11
    LL11a=select(LL11,L->not knownExample L);#LL11a
    last LL11a, last LL11 -- shows that all examples of genus 11 not covered by Plueger have multiplicity <= 10.

    elapsedTime nonWeierstrassSemigroups(5,11) -- 117.422 seconds elapsed - 
    LLdifficult={{6, 8, 17, 19, 21},{6, 8, 10, 19, 21, 23},{6, 9, 11, 14}}
    elapsedTime nonWeierstrassSemigroups(6,11,LLdifficult,Verbose=>true)   -- 267.818 seconds elapsed
    --(6, 11,  all but difficult semigroups are smoothable)
    elapsedTime LL611=select(LLdifficult,L->(<<L<<endl<<flush;elapsedTime not isWeierstrassSemigroup(L,0.4,Verbose=>true)));   -- 197.l321 seconds elapsed 

    elapsedTime nonWeierstrassSemigroups(7,11, LLdifficult, Verbose => true) --257 sec
    LLdifficult={{8, 9, 11, 15, 21}}
    elapsedTime nonWeierstrassSemigroups(8,11, LLdifficult, Verbose => true)
    LLdifficult={}
    elapsedTime nonWeierstrassSemigroups(9,11, LLdifficult, Verbose => true)
    LLdifficult={}
    elapsedTime nonWeierstrassSemigroups(10,11, LLdifficult, Verbose => true)
    ");
    )


    
///
restart
debug loadPackage( "NumericalSemigroups", Reload => true)
LL11=findSemigroups 11;#LL11
    LL11a=select(LL11,L->not knownExample L);#LL11a
    last LL11a, last LL11 -- shows that all examples of genus 11 not covered by Plueger have multiplicity <= 10.

LabBookProtocol 7
    LL7=findSemigroups 7;#LL7
    LL7a=select(LL7,L->not knownExample L);#LL7a
    elapsedTime LL7b=select(LL7a,L->not isSmoothableSemigroup(L,0.25,0,Verbose=>true))
    elapsedTime LL7b=select(LL7a,L->not isSmoothableSemigroup(L,0.25,0))
    LL7b=={}
      
    LL8=findSemigroups 8;#LL8
    LL8a=select(LL8,L->not knownExample L);#LL8a
    elapsedTime LL8b=select(LL8a,L-> not isSmoothableSemigroup(L,0.40,0)) -- 16.7345 seconds elapsed
    LL8b=={{6,8,9,11}}
    elapsedTime LL8c=select(LL8b,L-> not isWeierstrassSemigroup(L,0.15)) -- 1.88664 seconds elapsed
    LL8c=={} -- => every genus 8 semigroup is Weierstrass
    
    LL9=findSemigroups 9;#LL9
    LL9a=select(LL9,L->not knownExample L);#LL9a
    elapsedTime LL9b=select(LL9a,L->(not isSmoothableSemigroup(L,0.5,0)));#LL9b -- 134.401 seconds elapsed
    LL9b
    elapsedTime LL9c=select(LL9b,L->(not isSmoothableSemigroup(L,0.4,0)));  -- 26.7357 seconds elapsed
    LL9c=={} -- => every genus 9 semigroup is Weierstrass


    LL10=findSemigroups 10;#LL10
    LL10a=select(LL10,L->not knownExample L);#LL10a
    elapsedTime LL10b=select(LL10a,L-> elapsedTime not isSmoothableSemigroup(L,0.6,0)); -- 418.486 seconds elapsed
    #LL10b 
    elapsedTime LL10c=select(LL10b,L->(<<L<<endl<<flush;elapsedTime not isSmoothableSemigroup(L,0.5,0))); -- 173.422 seconds elapsed-
    #LL10c 
    elapsedTime LL10d=select(LL10c,L->(<<L<<endl<<flush;elapsedTime not isSmoothableSemigroup(L,0.45,0))); -- 156.571 seconds elapsed
    LL10d
    elapsedTime LL10e=select(LL10d,L->(<<L<<endl<<flush;elapsedTime not isWeierstrassSemigroup(L,0.4)));   -- 197.321 seconds elapsed 
    LL10e=={} -- => every genus 10 semigroup is Weierstrass

    elapsedTime nonWeierstrassSemigroups(5,11,Verbose =>true) -- 117.422 seconds elapsed - 

    LLdifficult={{6, 8, 17, 19, 21},{6, 8, 10, 19, 21, 23},{6, 9, 11, 14}}
    elapsedTime nonWeierstrassSemigroups(6,11,LLdifficult,Verbose=>true)   -- 267.818 seconds elapsed
    --(6, 11,  all but difficult semigroups are smoothable)
    elapsedTime LL611=select(LLdifficult,L->(<<L<<endl<<flush;elapsedTime not isWeierstrassSemigroup(L,0.4,Verbose=>true)));   -- 197.321 seconds elapsed 


    LLdifficult ={}
    elapsedTime nonWeierstrassSemigroups(7,11,LLdifficult,Verbose=>true)   -- 267.818 seconds elapsed
    elapsedTime LL711=select(LLdifficult,L->(<<L<<endl<<flush;elapsedTime not isWeierstrassSemigroup(L,0.4,Verbose=>true)));   -- 197.321 seconds elapsed 
    -- 951.724 seconds elapsed
    --o3 == {}

    LLdifficult ={{8, 9, 11, 15, 21}}
    elapsedTime nonWeierstrassSemigroups(8,11,LLdifficult,Verbose=>true)   
    elapsedTime LL811=select(LLdifficult,L->(<<L<<endl<<flush;elapsedTime not isWeierstrassSemigroup(L,0.4,Verbose=>true)));   -- 197.321 seconds elapsed 
    

    LLdifficult ={}
    elapsedTime nonWeierstrassSemigroups(9,11,LLdifficult,Verbose=>true)   
    elapsedTime LL911=select(LLdifficult,L->(<<L<<endl<<flush;elapsedTime not isWeierstrassSemigroup(L,0.4,Verbose=>true)));   -- 197.321 seconds elapsed 
    -- 998.636 seconds elapsed
    o4 = {}
    
        LLdifficult ={}
    elapsedTime nonWeierstrassSemigroups(10,11,LLdifficult,Verbose=>true)   
    elapsedTime LL1011=select(LLdifficult,L->(<<L<<endl<<flush;elapsedTime not isWeierstrassSemigroup(L,0.4,Verbose=>true)));   -- 197.321 seconds elapsed
    -- 2104.78 seconds elapsed
    --o5 == {}

    
     LLdifficult = {{6, 9, 17, 19, 20, 22},}
     elapsedTime nonWeierstrassSemigroups(6,12,LLdifficult,Verbose=>true)   
    elapsedTime LL612=select(LLdifficult,L->(<<L<<endl<<flush;elapsedTime not isWeierstrassSemigroup(L,0.4,Verbose=>true)));   -- 197.321 seconds elapsed 
   



 
    LLdifficult={}
    elapsedTime nonWeierstrassSemigroups(5,12,LLdifficult,Verbose=>true)  -- 152.485 seconds elapsed
    oo == {}
 
    LLdifficult={}
    elapsedTime nonWeierstrassSemigroups(7,12,LLdifficult,Verbose=>true)  -- 152.485 seconds elapsed
    oo == {}

   

makeUnfolding=method(Options =>
      {Verbose => false,
      "BaseField" => ZZ/(nextPrime 10007)})

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
        I:= trim ideal semigroupRing(L,"BaseField"=>o#"BaseField");
	makeUnfolding I)


-*
flatteningRelations1=method()
flatteningRelations1(Ideal,Ring, Matrix) := (I,A,unfolding) -> (
    gbI:=gb(I,ChangeMatrix=>true);
    S := ring I;
    SA := ring unfolding;
    chMat:=getChangeMatrix gbI;
    unfoldingGB := unfolding*sub(chMat,SA);
    ldT := flatten entries leadTerm unfoldingGB;
    s0:=syz sub(gens gbI,SA);s1:=null;
    --Now we compute the Buchberger test syzygies
    us:=null;testSyzygy1:=null;u1:=null;
    while (
	testSyzygy1=unfoldingGB*s0;
	us=apply(ldT,u->(u1=contract(u,testSyzygy1);
	   testSyzygy1=testSyzygy1-u*u1;
	   u1));
        s1=fold(us,{i,j}->i||j);
	not s1 == 0 ) do (
	s0 = s0-s1);
    --The flatteningRelations are the coefficients of testSyzygy2
    testSyzygy2:=unfoldingGB*s0;
    ma := max flatten degrees source syz leadTerm gens gbI;
    rems := reverse flatten for i from 0 to ma list (b:=basis(i,S^1/I); if b==0 then  continue else (entries b))_0;
    us = apply(rems,u->(u1:=contract(sub(u,SA),testSyzygy2);testSyzygy2-sub(u,SA)*u1;
	u1));
    relsA:=sub(ideal(flatten us),A);
    relsA
     )
*-

flatteningRelations=method()
flatteningRelations(Ideal,Ring, Matrix) := (I,A,unfolding) -> (
    gbI:=gb(I,ChangeMatrix=>true);
    S := ring I;
    SA := ring unfolding;
    chMat:=getChangeMatrix gbI;
    unfoldingGB := unfolding*sub(chMat,SA);
    -- can one use the build in gb algorithm to copute the
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




isSmoothableSemigroup=method(Options =>
      {Verbose => false,
      "BaseField" => ZZ/(nextPrime 10007)})

isSmoothableSemigroup(List,RR,ZZ) := o-> (L,r,n) -> (
    (I,J1,family) := getFlatFamily(L,r,n,o);
    isARandomFiberSmooth(I,J1,family,o))


      -* Documentation section *-
end--
restart
needsPackage "SmoothabilityOld"

beginDocumentation()
-*
document {
Key => SmoothabilityOld,
Headline => "Compute invariants of a numerical semigroup",
   "In this package we consider numerical semigroups: that is, cofinite subsets of the natural numbers that are closed under sums.
   We generally refer to these simply as semigroups.
   
   A semigroup S thus includes the empy sum, 0, but we input semigroups by giving generators, all nonzero.
   The smallest nonzero element of S is the multiplicity. The Apery set (really sequence) of a semigroup S is the
   the list {a_1..a_m-1} where a_i is the smallest element in S such that a_i = i mod m.
   The conductor is 1 plus the largest element not in S. We generally specify a semigroup by giving
   a list of positive integers L with gcd = 1, representing the semigroup of all sums of
   elements of L.",
   
   PARA{},
     SUBSECTION "Weierstrass semigroups",
     "The question whether every semigroup is a Weierstrass semigroup was answered negatively 
     by Buchweitz: the semigroup generated by {13, 14, 15, 16, 17, 18, 20, 22, 23} is not a Weierstrass semigroup,
     as demonstrated in ", TO buchweitz,".
     On the other hand Pinkham gave a positve criterion with deformation theory.
     A semigroup is a Weierstrass semigroup if and only if the graded semigroup ring of L 
     has a smoothing deformation with strictly positive deformation parameters.",
     PARA{},

     "In this section we implemented Pinkham's approach in POSITIVE CHARACTERISTIC. We plan
     to extend the smoothing results to characteristic 0 in the future.",
     UL{
	TO makeUnfolding,
	TO flatteningRelations,
        TO getFlatFamily,
	TO findPoint,
	TO isARandomFiberSmooth,
	TO heuristicSmoothness,
--	TO isSmoothableSemigroup,
	TO isWeierstrassSemigroup,
	TO nonWeierstrassSemigroups,
	TO LabBookProtocol,
        }     
}
*-

doc ///
Key
 LabBookProtocol
 (LabBookProtocol, ZZ)
Headline
 Prints code that finds Weierstrass Semigroups in (low) genus g
Usage
 s = LabBookProtocol g
Inputs
 g:ZZ
  genus
Outputs
 s:String
  commands to study semigroups of genus g
Description
  Text
   This function prints a series of commands that check that most semigroups of genus g (up to g = 10) are Weierstrass.
   It outputs a short list of "difficult" examples that currently take too long to check.
  Example
   LabBookProtocol 7
   LL7=findSemigroups 7;#LL7
   LL7a=select(LL7,L->not knownExample L);#LL7a
   elapsedTime LL7b=select(LL7a,L->not isSmoothableSemigroup(L,0.25,0,Verbose=>true))
   elapsedTime LL7b=select(LL7a,L->not isSmoothableSemigroup(L,0.25,0))
   LL7b=={}
  Text
    With the option Verbose=>true one gets timings on various parts of the computation.
    To check all semigroups of genus g=8,9 and 10 takes about

    18.2, 161.1 and 945.6 seconds respectively.

  Example
   LabBookProtocol 11
  Text
   Since the number of cases gets rather large, we break up the list of all semigroups
   into sublists of semigroups of given multiplicity and call the function nonWeierstrassSemigroups:
  Example
   m=5,g=8
   elapsedTime nonWeierstrassSemigroups(m,g,Verbose=>true)
  Text
   In the verbose mode we get timings of various computation steps and further information.
   The first line,
   (13,1),
   indicates that there 13 semigroups of multiplicity 5 and genus 8 of which only 1 is not flagged
   as smoothable by the function knownExample.
   The second line,
   {5,8,11,12},
   gives the current semigroup.
   The timing under various  headers tells how much time was used in each of the steps.
  Example
   L={6,8,9,11}
   genus L
   isWeierstrassSemigroup(L,0.2,Verbose=>true)
  Text
   The first integer, 6, tells that in this attempt deformation parameters of degree >= 6 were used and no smooth fiber was found.
   Finally with all parameters of degree >= 4, the flatteningRelations define a scheme that decomposes into 2 components,
   both affine spaces. If we encounter non affine components we print  "has to solve", and find a point in each such component.
   We then print the number of singular points in the fiber.
   Finally the output "{0,-1}" is the dimension of the singular loci of a random fiber over each component.
   Thus the entry "-1" indicates that a general fiber of the second component is smooth.
   
SeeAlso
  isSmoothableSemigroup
  isWeierstrassSemigroup
  nonWeierstrassSemigroups
  knownExample
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
  genus
Outputs
 b:Boolean
  true if L is a known example of a Weierstrass semigroup
Description
  Text
   Certain semigroups are known to be Weierstrass. For example L has 2  or 3 generators only, by work of Pinkham and Sally. 
   Another sort examples are semigroup with small weight ewt(L) < genus L by the work Nathan Pflueger extending
   work of Eisenbud-Harris.
  Example
   L={7,12,13}
   knownExample L
   L={7,8,9,11,13}
   ewt L, genus L
   knownExample L
   LL=findSemigroups(9,10);#LL
   select(LL,L->not knownExample L)
   #oo
SeeAlso
  LabBookProtocol
  findSemigroups
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

       3*(genus L-1) -#sums(G,G) >=0.

   The function returns this difference.  

  Example
   L={7,12,13}
   buchweitzCriterion L
   L= buchweitz 0
   buchweitzCriterion L
   (H,M)=allSemigroups L
   b=(entries M)_0
   g=(entries H)_0
   apply(3,i->buchweitzCriterion(13,b+i*g))

SeeAlso
  buchweitz
///
doc ///
Key
 def1
 (def1, List)
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
   T^1(B) is the tangent space to the versal deformaion of
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
 makeUnfolding
 (makeUnfolding, Ideal)
 (makeUnfolding, List) 
 [makeUnfolding, "BaseField"]
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
   Given a (quasi)homogenous ideal in a ring S = kk[x_0..x_n]
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
 J= flattening(I,A,unfolding)
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
 isSmoothableSemigroup
 (isSmoothableSemigroup, List, RR, ZZ)
 [isSmoothableSemigroup, "BaseField"]
 [isSmoothableSemigroup, Verbose ]
Headline
 Look for a smoothing family
Usage
 b=isSmoothableSemigroup(L,r,n)
Inputs
 L:List
   the generators of a semigroup
 r:RR
 n:ZZ
   numbers which influences the truncation
Outputs
 b: Boolean
   true if a smoothing family was found, false no smoothing family was found
Description
  Text
    After computing an unfolding and restricting the
    unfolding to variables of degree larger than
    
             (maximal degree of a parameter)*r+n,
	     
    we compute the flattening relations J of the restricted unfolding.
    If J defines a union of components X,
    we check whether the fiber over a random closed point of each X is smooth.
    If we find a smooth fiber we return true, else we return false.
  Example
    L={6,8,9,11}
    genus L
    elapsedTime isSmoothableSemigroup(L,0.30,0)
    elapsedTime isSmoothableSemigroup(L,0.14,0)
SeeAlso
 makeUnfolding
 flatteningRelations
 getFlatFamily
 isARandomFiberSmooth
 ///


doc ///
Key
 isWeierstrassSemigroup
 (isWeierstrassSemigroup, List, RR)
 [isWeierstrassSemigroup, "BaseField"]
 [isWeierstrassSemigroup, Verbose]
Headline
 Experimentally decide whether L is a Weierstrass semigroup
Usage
 b=isWeierstrassSemgroup(L,r)
Inputs
 L:List
   the generators of a semigroup
 r:RR
   numbers which influences the truncation
Outputs
 b: Boolean
   true if a smoothing family was found, false no smoothing family was found
Description
  Text
    After computing an unfolding we successivly restricting the
    unfolding to variables of degree larger  an integer n  for an n with
    
             n<=(maximal degree of a parameter)*r,
	     
    compute the flattening relations J of the restricted unfolding.
    If J defines a union of components X,
    we check whether the fiber over a random closed point of each X is smooth.
    If we find a smooth fiber we return true, else we continue with n-1 until we checked
    the full unfolding.
  Example
    L={6,8,9,11}
    genus L
    elapsedTime isWeierstrassSemigroup(L,0.15)
SeeAlso
 makeUnfolding
 flatteningRelations
 getFlatFamily
 isARandomFiberSmooth
 ///

doc ///
Key
 nonWeierstrassSemigroups
 (nonWeierstrassSemigroups, ZZ,ZZ)
 (nonWeierstrassSemigroups, ZZ,ZZ,List)
 [nonWeierstrassSemigroups, "BaseField"]
 [nonWeierstrassSemigroups, Verbose]
Headline
 Find possibly non Weierstrass Semigroups
Usage
 LL=nonWeierstrassSemgroups(m,g)
 LL=nonWeierstrassSemgroups(m,g,LLdifficult)
Inputs
 m:ZZ
   the multiplicity of a semigroup
 g:ZZ
   the genus of a semigroup
 LLdifficult: List
   List of difficult semigroups which we exclude from the test
Outputs
 LL: List
   List of possible non Weierstrass semigroups including LLdifficult
Description
  Text
    We test which semigroups of multiplicity m and genus g are smoothable.
    If no smoothing was found then L is a candidate for a non Weierstrass semigroup.
    In this search certain semigroups L in LLdifficult, where the computation is particular heavy are
    excluded.
  Example
    elapsedTime nonWeierstrassSemigroups(6,7)
    LLdifficult={{6, 8, 9, 11}}
    elapsedTime nonWeierstrassSemigroups(6,8,LLdifficult,Verbose=>true)
  Text
   In the verbose mode we get timings of various computation steps and further information.
   The first line,
   (17,5),
   indicates that there 17 semigroups of multiplicity 6 and genus 8 of which only 5 is not flagged
   as smoothable by the function knownExample.
   The second line,
   {6, 7, 8, 17},
   gives the current semigroup.
   The timing under various  headers tells how much time was used in each of the steps.   
SeeAlso
 isWeierstrassSemigroup
 LabBookProtocol
 ///
doc ///
Key
 getFlatFamily
 (getFlatFamily, List, RR, ZZ)
 [getFlatFamily, "BaseField"]
 [getFlatFamily, Verbose ]
Headline
 Compute the flat family depending on a subset of parameters of the universal unfolding
Usage
 (I,J1,family)=getFlatFamily(L,RR,ZZ)
Inputs
 L:List
   the generators of a semigroup
 r:RR
 n:ZZ
   numbers which influences the truncation
Outputs
 I: Ideal
    semigroup ideal
 J1:Ideal
    flatness relations among the parameters
 family: Matrix
    defining equation of the family
Description
  Text
    After computing an unfolding and restricting the
    unfolding to variables of degree larger than
    
             (maximal degree of a parameter)*r+n,
    
    we compute the flattening relations and remove dependent variables.
    The remaining flattening relation are returned in the ideal J1.
    Using the function isARandomFiberSmooth we then can check with good luck
    whether a random fiber over some component of J1 is smooth.
  Example
    L={6,8,10,11}
    genus L
    (I,J1,family)=getFlatFamily(L,0.30,0);
    betti res ideal family == betti res I
    isARandomFiberSmooth(I,J1,family)
    support family
    support family /degree
    gens ring J1 /degree
  Text
    Parameters of the universal unfolding of degree <= 22*0.3 are not used
  Example
    (I,J1,family)=getFlatFamily(L,0.00,11);
    support family
    support family /degree
  Text
    Parameters of the universal unfolding of degree < 11) are not used
  Example
    isARandomFiberSmooth(I,J1,family)
    A = ring family
    transpose family
SeeAlso
 makeUnfolding
 flatteningRelations
 getFlatFamily
 isARandomFiberSmooth
 ///

doc ///
Key
 isARandomFiberSmooth
 (isARandomFiberSmooth, Ideal, Ideal, Matrix)
 [isARandomFiberSmooth, "BaseField"]
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
    genus L
    (I,J1,family)=getFlatFamily(L,0.30,0);
    isARandomFiberSmooth(I,J1,family)
    SA=ring family
    transpose family
SeeAlso
 makeUnfolding
 flatteningRelations
 getFlatFamily
 ///

 doc ///
Key
  heuristicSmoothness
  (heuristicSmoothness, Ideal)
  [heuristicSmoothness, "BaseField"]
  [heuristicSmoothness, Verbose ]
Headline
  Check whether an affine curve is smooth
Usage
  b=heuristicSmoothness c
Inputs
  c: Ideal
    of an affine curve
Outputs
  b: Boolean
    true if the computation showes that c is smooth false otherwise
Description
  Text
    We  check for smoothness using only some of the minors of
    the jacobian matrix. If we are lucky this establishes smoothness.
    With bad luck we might fail even in case when c is smooth.   
  Example
    kk=ZZ/2; S=kk[x_0..x_3]
    setRandomSeed "some singular and some smooth curves";
    elapsedTime tally apply(10,i-> (
	    c=minors(2,random(S^2,S^{3:-2}));
	    c=sub(c,x_0=>1);
	    R=kk[support c];c=sub(c,R);
	    heuristicSmoothness c))

///
TEST///-*test of findPoint*-
kk=ZZ/101
R=kk[x_0..x_5]
setRandomSeed 0
c=ideal random(R^1,R^{2:-1,2:-2})
point=findPoint c
assert(sub(c,point)== 0)
///	

TEST///-*flattening and unfolding*-
assert ((L = mingens {5,6, 8,9, 10,12, 13, 17}) == {5, 6, 8, 9})
I=semigroupIdeal L
(A,unfolding)=makeUnfolding I;
assert(numgens A == 68)
J=flatteningRelations(I,A,unfolding);
numgens J
assert(numgens J == 260)
///
TEST ///-* Buchweitz example of nonsmoothable semigroup and isGapSequence*-
G=toList(1..12)|{19,21,24,25}
L=isGapSequence G
G1=gaps L
G1==G
assert(#sums(G1,G1)>3*(#G1-1))
///

      end--

      -* Development section *-
      restart
      debug needsPackage "SmoothabilityOld"
      check "SmoothabilityOld"

      uninstallPackage "SmoothabilityOld"
      restart
      installPackage "SmoothabilityOld"
      viewHelp "SmoothabilityOld"
