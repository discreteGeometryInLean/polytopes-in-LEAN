# Polytopes in LEAN

The goals are:
- to provide (preferably very general) definitons for polytopes, polyhedra and cones.
- to prove the Minkowski-Weyl theorem for these classes of objects (i.e. V-polytope = H-polytope).
- to provide the fundamental definitions and lemmas of Polytope Theory (faces, face lattice, combinatorial equivalence, normal/face fan, polar duality, etc.)

An initial task will be to figure out how general our implementation should be. If feasible, we aim for
- polytopes and polyhedra in affine spaces (instead of linear spaces, though the current implementation of affine spaces in LEAN is lacking)
- no inner products (one can work with dual space instead of normal vectors for most needs of "combinatorial" polytopes theory)
- no metric (we need a PL alternative for "bounded")
- no topology (we need a PL alternative for "boudnary", "realative interior" etc.)

One might consider to be even more general, if feasible:
- tropical polytopes (that is, the base space is over a semi-ring)
- spherical/projective polytopes
- hyperbolic polytopes
