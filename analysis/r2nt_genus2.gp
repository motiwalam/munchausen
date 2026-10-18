\\ Question 32, n = 5: the curve U^2 = 4x^5 + x^2 + 4, that is b^2 + x b = x^5 + 1.
\\ Prints the minimal model and conductor (genus2red), small rational points,
\\ and the analytic rank of the Jacobian (numerical, lfunorderzero).
\\ Also the n = 3 elliptic curve Y^2 = X^3 + X^2 + 64 (X = 4x): rank.
\\ usage: gp -q < analysis/r2nt_genus2.gp   (about 1 minute)
default(parisizemax, 2*10^9);
f = 4*x^5 + x^2 + 4;
print("genus2red: ", genus2red(f));
print("rational points with height <= 10^4: ", hyperellratpoints(f, 10^4));
L = lfungenus2([x^5 + 1, x]);
print("analytic rank of J (n = 5): ", lfunorderzero(L));
E = ellinit([0, 1, 0, 0, 64]);
print("n = 3 curve: conductor ", ellglobalred(E)[1], ", rank bounds ", ellrank(E)[1..2]);
\q
