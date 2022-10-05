load "library.m";
SetColumns(0);

AliceSecret := RandomBits(25);
"Starting attack with randomly generated secret: ", AliceSecret;

/*
* Parameters.
*/
p := 24554940634497023;
K := GF(p^2);
_<x> := PolynomialRing(K);

E := EllipticCurve([ 7227205329032435*K.1 + 15319231758733382, 1613665374322417*K.1 + 13936835279929152 ]);

PA := E![ 20746884927937558*K.1 + 10366606564223489, 2983063898332369*K.1 + 347565651777734 ];
QA := E![ 23304177781423091*K.1 + 15534658969717044, 3911681224067712*K.1 + 2003638603203939 ];
PB := E![ 16339026551876410*K.1 + 7944249485412187, 13601096240661708*K.1 + 20561857423119867 ];
QB := E![ 23433067763028489*K.1 + 803842936998551, 4886333153359413*K.1 + 7470641555206833 ];

// Number of bits
eA := Ceiling(Log(2, AliceSecret));

ord := Factorisation(p+1)[1,2];

if eA gt ord then
	"Secrets are too large";
	exit;
end if;

P := 2^(ord-eA)*PA;
Q := 2^(ord-eA)*QA;

_A := P+AliceSecret*Q;

E_0, psi := LongIsogeny(_A, 2^eA);
jE_0 := jInvariant(E_0);

/*!
* The ORACLE.
*/
Oracle := function(R, S, ordR : a := AliceSecret)
	E, _ := LongIsogeny(R + a*S, ordR);
	return jInvariant(E);
end function;

// clear the secrets to prove that they are not used in the attack
AliceSecret := 0;
_A := 0;
psi := 0;
K := 0;
a := [];

start_time := Realtime();

/*!
 * Recover one bit of the secret.
 */
recover_bit := function(n, jE_0, K, P, Q, eA)
	jInv := Oracle(P - K*(2^(eA-n))*Q, (1+2^(eA-n))*Q, 2^eA);
	if jInv eq jE_0 then return 0;
	else return 1;
	end if;	
end function;


// Walk backwards and recover every bit
for n in [1..eA] do
	a; // Print out current bits recovered for debugging.
	"Finding bit", n, "... Time elapsed:", Realtime(start_time);
	K := pListToDec(a,2);
	Append(~a, recover_bit(n, jE_0, K, P, Q, eA));
end for;

//This should be it once we reach here.
"Recovered secrets:", pListToDec(a, 2);


"Total time elapsed:", Realtime(start_time);
