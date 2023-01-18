R(0, 0, b, b).
R(k + 1, r1, k + b + 1, r2) :- R(k, r1 - (k + 1), k + b, r2 - (k + b + 1)), k >= 0.
?- R(k, r1, k + b, r2), k = n, k = m - b, b = 0, n = m, r1 \= r2.
