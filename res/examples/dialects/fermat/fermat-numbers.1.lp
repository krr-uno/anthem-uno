% F_n = k
nth_fermat(0,3).
nth_fermat(N,K) :- K = (Y-1)*(Y-1) + 1, nth_fermat(N-1,Y), N = 1..n.

% k is a Fermat number
fermat(K) :- nth_fermat(N,K), N = 0..n.
