# Question 51: n = 3. U^2 = 4 x^3 + x^2 + 4c becomes Y^2 = X^3 + X^2 + 64 c
# with X = 4x, Y = 4U. The integral points with X = 4x, x >= 1, give the
# solutions b = (U - x)/2 of b(b+x) = x^3 + c.
# usage: sage analysis/r3nt_n3.sage
for c in (1, 3, 25):
    E = EllipticCurve([0, 1, 0, 0, 64 * c])
    pts = E.integral_points()
    sols = []
    for P in pts:
        X, Y = ZZ(P[0]), abs(ZZ(P[1]))
        if X > 0 and X % 4 == 0 and Y % 4 == 0:
            x, U = X // 4, Y // 4
            if (U - x) % 2 == 0 and U > x:
                sols.append((x, (U - x) // 2))
    print("c = %d: conductor %d, rank %d, %d integral points; solutions (x, b) with x >= 1: %s"
          % (c, E.conductor(), E.rank(), len(pts), sorted(sols)))
