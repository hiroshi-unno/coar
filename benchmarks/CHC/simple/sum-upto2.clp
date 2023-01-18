R(0, n, n, 0).
R(k, n, s1 + n - k, s2 + k) :- R(k - 1, n, s1, s2), k >= 1.
?- R(k, n, s1, s2), s2 \= s1.
