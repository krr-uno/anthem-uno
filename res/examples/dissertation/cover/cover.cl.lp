{incover(1..n)}.
           :- I < J, incover(I), incover(J), s(X,I), s(X,J).
           :- s(X,J); not s(X,I) : incover(I).
