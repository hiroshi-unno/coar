R(n, 0, 0, a, a).
R(n, m + 1, n + s1, a, s2) :- R(n, m, s1, a + n, s2).
?- R(n, m, s1, 0, s2), s1 \= s2.
