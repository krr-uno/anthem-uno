% F_n = k
nth_fermat(0,3).
nth_fermat(1,5).
nth_fermat(N,K) :- K = Y*Y - 2*(X-1)*(X-1), nth_fermat(N-1,Y), nth_fermat(N-2,X), N = 1..n.

% k is a Fermat number
fermat(K) :- nth_fermat(N,K), N = 0..n.
