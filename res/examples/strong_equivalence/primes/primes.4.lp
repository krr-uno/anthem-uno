composite(I*J) :- I=2..10, J=2..10.
prime(N) :- N=2..10, not composite(N).
