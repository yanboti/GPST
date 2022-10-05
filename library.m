/*!
* Find a usable SIDH prime.
*/
FindPrime := function(NumBits)
	TwoPow := Ceiling(NumBits/2);
	ThreePow := Ceiling(NumBits/Log(2,3));
	PrimeList := PrimesUpTo(500);
	for ind in [1..5] do
		for f in PrimeList do
			p := Power(2, TwoPow)*Power(3, ThreePow)*f - 1;
			if IsPrime(p) then
				return p;
			end if;
		end for;
		TwoPow +:= 1;
	end for;
	return 0;
end function;

/*!
* Generate a random supersingular elliptic curve over L.
*/
Random_SS_Curve := function(L)
	E := EllipticCurveWithjInvariant(L!1728);
	if not IsSupersingular(E) then
		E := EllipticCurveWithjInvariant(L!0);
	end if;
	if not IsSupersingular(E) then
		"Failed to generate supersingular curve!";
		return 0;
	end if;

	NumIter := Ceiling(Log(2, Characteristic(L)));
	_<x> := PolynomialRing(L);
	for i in [0..NumIter] do
		S := DivisionPoints(E!0, 2)[Random([2,3,4])];
		ker := (x-S[1]);
		E, _ := IsogenyFromKernel(E, ker);
	end for;
	return E;
end function;

/*!
* Generate SIDH generators.
*/
GetSIDHGenerators := function(J : ComputeBPts:=true)
	p := Characteristic(BaseRing(J));
	Ord_fact := Factorisation(p+1);
	pA := Ord_fact[1, 1];
	eA := Ord_fact[1, 2];
	pB := Ord_fact[2, 1];
	eB := Ord_fact[2, 2];
	AOrd := Power(pA, eA);
	BOrd := Power(pB, eB);

	// Generating points PA, QA
	ATor := DivisionPoints(J!0, AOrd);
	for P in ATor do
		if Order(P) ne AOrd then continue; end if;
		for Q in ATor do
			if Order(Q) ne AOrd then continue; end if;
			if not IsLinearlyIndependent(P, Q, AOrd) then continue; end if;
			A_Pts := [P, Q];
			break P;
		end for;
	end for;

	// Generating points PB, QB
	if ComputeBPts then
		BTor := DivisionPoints(J!0, BOrd);
		for P in BTor do
			if Order(P) ne BOrd then continue; end if;
			for Q in BTor do
				if Order(Q) ne BOrd then continue; end if;
				if not IsLinearlyIndependent(P, Q, BOrd) then continue; end if;
				B_Pts := [P, Q];
				break P;
			end for;
		end for;
	else
		B_Pts := [];
	end if;

	return A_Pts, B_Pts;
end function;

/*!
* Get canonical supersingular representative.
*/
GetSSRepFromjInv := function(jInv)
	p := Characteristic(Parent(jInv));
	E := EllipticCurveFromjInvariant(jInv);
	P := [Random(E) : ind in [1..10]];
	if &and[(p+1)*Pind eq E!0 : Pind in P] then
		return E;
	else
		ind := 1;
		alp := PrimitiveElement(BaseRing(E));
		repeat
			ind +:= 1;
			Et := QuadraticTwist(E, alp^ind);
			P := [ Random(Et) : jnd in [1..10] ];
		until &and[ (p + 1)*Pind eq Et!0 : Pind in P ];
		return Et;
	end if;
end function;

/*!
* Compute 'small' isogeny.
*/
SmallIsogeny := function(P, deg)
	E := Curve(P);

	if deg eq 1 then
		return E;
	elif deg*P ne E!0 then
		return 0;
	end if;

	K := BaseRing(E);
	_<x> := PolynomialRing(K);

	C, phi := IsogenyFromKernel(E, &*[ x - (ind*P)[1] : ind in [1..deg-1] ]);
	//We would like to ensure that the the Codomain is the EXACT curve we want to work in.
	Cj := GetSSRepFromjInv(jInvariant(C));
	if IsIsomorphic(C, Cj) then
		_, theta := IsIsomorphic(C, Cj);
		phi := phi*theta;
		return Cj, phi;
	else
		"WARNING: [SmallIsogeny] Cannot make codomain the canonical one.";
		return C, phi;
	end if;
end function;

/*!
* Compute 'long' isogeny.
*/
LongIsogeny := function(P, deg)
	pA := Factorisation(deg)[1,1];
	eA := Factorisation(deg)[1,2];

	phis := [**];
	for ind in [1..eA] do
		C, phi := SmallIsogeny(pA^(eA-ind)*P, pA);
		P := phi(P);
		Append(~phis, phi);
	end for;

	return C, phis;
end function;

/*!
* Evaluate 'long' isogeny.
*/
EvaluateLongIsogeny := function(phis, P)
	for phi in phis do
		P := phi(P);
	end for;
	return P;
end function;

/*!
* Converts a p-ary representation to a decimal.
*/
pListToDec := function(a, p)
	val := 0;
	for ind in [1..#a] do
		val +:= Power(p, ind - 1)*a[ind];
	end for;
	return val;
end function;
