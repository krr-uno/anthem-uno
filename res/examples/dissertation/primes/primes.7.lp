composite(I*J) :- I = 2..b, J = 2..N, I*N = b.
      prime(I) :- I = a..b, not composite(I).
