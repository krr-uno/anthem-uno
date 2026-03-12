composite(I*J) :- I = 2..b, J = 2..b/I.
      prime(I) :- I = a..b, not composite(I).
