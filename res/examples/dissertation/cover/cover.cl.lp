{in_cover(1..n)}.
           :- I < J, in_cover(I), in_cover(J), s(X,I), s(X,J).
           :- s(X,J); not s(X,I) : in_cover(I).
