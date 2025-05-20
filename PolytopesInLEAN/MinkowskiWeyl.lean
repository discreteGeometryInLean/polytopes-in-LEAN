
import PolytopesInLEAN.Polyhedron
import PolytopesInLEAN.Polytope

variable {𝕜 : Type*} [LinearOrderedField 𝕜]
variable {V : Type*} [VectorSpace 𝕜 V]
variable {A : Type*} [AffineSpace V A]

-- One direction of Minkowski-Weil Theorem
theorem Polyhedron.bounded_is_polytope (P : Polyhedron A) (h_bd : Set.ray_bounded P.1)
    : Set.is_polytope P.1 := by
  -- 1. If the polyhedron P is bounded, then the ambient space is of finite dimension.
  -- This is important because the proof is by induction on this finite dimension.
  have FiniteDimensional := P.ray_bounded_impl_finite_dim h_bd
  -- 2. Induction on dimension of ambient space
  generalize h_dim : AffineSpace.dim A = n
  induction n generalizing V A h_bd
  case zero => -- Indunction start
    -- All subsets of 0-dim affine space are polytopes
    --apply AffineSpace.subset_of_dim_zero_is_polytope
    --exact h_dim
    sorry
  case succ n ih => -- Induction step
    sorry

def Polytope.from_polyhedron {P : Polyhedron A} (h_bd : Set.ray_bounded P.1)
  : Polytope A := ⟨ P.1, P.bounded_is_polytope h_bd ⟩

-- Other direction of Minkowski-Weil Theorem
theorem Polytope.is_polyhedron (P : Polytope A) : Set.is_polyhedron P.1 := by
  sorry
