{incover(1..n)}.
           :- I != J, incover(I), incover(J), s(X,I), s(X,J).
covered(X) :- incover(I), s(X,I).
           :- s(X,I), not covered(X).
