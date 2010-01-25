%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Encoding for checking whether variable x_k evaluates to 0 for
% a disjunctive BES.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% 10.2.2004
% assumes that dependencies are encoded as follows
% ddep(i,j). ddep(i,k). facts for a disjunctive equation 
% 1{ cdep(i,j), cdep(i,k)} 1. pcdep(i,j). pcdep(i,k).
% for a conjunctive equation 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% depends(Y) holds when x_k depends on x_Y
depends(Y) :-
        ddep(X,Y), solve(X).
depends(Y) :-
        pcdep(X,Y), % domain predicates
        cdep(X,Y), solve(X).
depends(Y) :-
        depends(W), ddep(W,Y).
depends(Y) :-
        pcdep(W,Y), % domain predicates
        depends(W), cdep(W,Y).

% reached(X,Y) holds when
% Y is reached via dep from X through nodes Z >= X
reached(X,Y) :-
        nu(X), ddep(X,Y), Y>=X.
reached(X,Y) :-
        pcdep(X,Y), % domain predicates
        nu(X), cdep(X,Y), Y>=X.
reached(X,Y) :-
         nu(X), Z >=X,  % domain predicates
         reached(X,Z), ddep(Z,Y), Y>=X.
reached(X,Y) :-
         nu(X), pcdep(Z,Y), Z >=X,  % domain predicates
         reached(X,Z), cdep(Z,Y), Y>=X.

% In a stable model it CANNOT be the case that there is a nu variable x_Y
% such that x_k depends on it and it is self-dependent.
:- depends(Y), reached(Y,Y), nu(Y).