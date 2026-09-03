% 2^k = X
exp(1,2).
exp(K,X) :- X = 2*Y, exp(K-1,Y), K = 1..m.

% Primes
composite(I*J) :- I = 2..z, J = 2..z/I.
prime(I) :- I = 2..z, not composite(I).

% 2^k + 1 = X
fermat(X) :- prime(X), X = Y+1, exp(K,Y).
