
--Choose a prime p >=3
--(a) Then {2p,3p,4p+c,5p+c} is NW for all c with c mod p != 0. 
--or (b) {2p,3p,3p+c,4p+c} is NW for all c with c mod p != 0. except for p=2, fails for the first 2 instances
--

--(a) {2p,3p,4p+c,5p+c} --no 
for p from 3 to 100 do(
    if isPrime(p) == false then continue;
    a := 2*p;
    b := 3*p;
    for i from 1 to 100 do(
	if i % p == 0 then continue;
	c = 4*p+i;
	d = 5*p+i;
	print testNWfWithAllDegreeConditions {a,b,c,d};
	)
    )

--(b){2p,3p,3p+c,4p+c}
for p from 3 to 100 do(
    if isPrime(p) == false then continue;
    a := 2*p;
    b := 3*p;
    for i from 1 to 100 do(
	if i % p == 0 then continue;
	c = 3*p+i;
	d = 4*p+i;
	print testNWfWithAllDegreeConditions {a,b,c,d};
	)
    )

--for p >= 5
--{2p,3p,4p+c,9p+2c} is NW for all c with c mod p != 0


for p from 5 to 100 do(
    if isPrime(p) == false then continue;
    a := 2*p;
    b := 3*p;
    for i from 1 to 100 do(
	if i % p == 0 then continue;
	c = 4*p+i;
	d = 9*p+2*i;
	print testNWfWithAllDegreeConditions {a,b,c,d};
	)
    )


--for p >= 7
--{2p,3p,4p+c,13p+3c} is NW for all c with c mod p != 0
for p from 7 to 100 do(
    if isPrime(p) == false then continue;
    a := 2*p;
    b := 3*p;
    for i from 1 to 100 do(
	if i % p == 0 then continue;
	c = 4*p+i;
	d = 13*p+3*i;
	print testNWfWithAllDegreeConditions {a,b,c,d};
	)
    )


--for p >= 11
for p from 11 to 100 do(
    if isPrime(p) == false then continue;
    a := 2*p;
    b := 3*p;
    for i from 1 to 100 do(
	if i % p == 0 then continue;
	c = 3*p+i;
	d = 13*p+4*i;
	print testNWfWithAllDegreeConditions {a,b,c,d};
	)
    )

----------------------------IGNORE ----------------------------------------------------------------
---testing/scratch
for p from 3 to 100 do(
    if isPrime(p) == false then continue;
    a := 2*p;
    b := 3*p;
    for c from b+1 to 100 do(
	for d from c+1 to 200 do(
	   r =   testNWfWithAllDegreeConditions {a,b,c,d};
	   if r#1  == true then(
	       i := c-4*p;
	       j := d-5*p;
	       k5 := (d-9*p)/2;
	       k7 := (d-13*p)/3;
	       k11 :=(d-13*p)/4;
	       if i != j and i != k5 and i != k7 then (
		   print testNWfWithAllDegreeConditions {a,b,c,d};
		   print {i,j};
		   print {i,k5};
		   print {i,k7};
		   print {i,k11}
		   )
	       )
	   )
       )
   )




for p from 5 to 100 do(
    if isPrime(p) == false then continue;
    a := 2*p;
    b := 3*p;
    for i from 1 to 100 do(
	if i % p == 0 then continue;
	c = 4*p+i;
	d = 9*p+2*i;
	print testNWfWithAllDegreeConditions {a,b,c,d};
	)
    )

for p from 7 to 100 do(
    if isPrime(p) == false then continue;
    a := 2*p;
    b := 3*p;
    for i from 1 to 100 do(
	if i % p == 0 then continue;
	c = 3*p+i;
	d = 10*p+3*i;
	print testNWfWithAllDegreeConditions {a,b,c,d};
	)
    )
