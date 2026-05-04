composite(I*J) :- I=2..10000, J=2..10000/I.
prime(N) :- N=2..10000, not composite(N).
