
import PolytopesInLEAN.Aux_General
import PolytopesInLEAN.Aux_Convex

noncomputable section

/- We assume all propositions are decidable to properly work with Finset:
  * allows to freely convert between Finset and Set.Finite.
  * allows us to recognize {P, Q} has a Finset, even if P and Q
    have no decidable equivalence natively.
-/
attribute [local instance] Classical.propDecidable

variable {𝕜 : Type*} [LinearOrderedField 𝕜]
variable {V : Type*} [VectorSpace 𝕜 V]
variable {A : Type*} [AffineSpace V A]

-- Polytopes --

def Set.is_polytope (S : Set A)
  := ∃ set : Set A,
      set.Finite ∧
      S = convex_hull set

-- abbrev Polytope (A : Type*) [AffineSpace V A] -- = V-Polytopes
--   := { S : Set A // is_polytope S }

structure Polytope (A : Type*) [AffineSpace V A] where
  set : Set A
  is : set.is_polytope
instance : Coe (Polytope A) (Set A) := ⟨Polytope.set⟩

theorem Polytope.is_convex (P : Polytope A) : P.1.is_convex := by
  let ⟨ S, _, _, hS ⟩ := P
  dsimp; rw [hS]
  apply convex_hull.is_convex

/-- A definition of 'being bounded' in affine spaces that does not require
  a topology. -/
def poly_bounded (S : Set A) := ∃P : Polytope A, S ⊆ P

lemma Polytope.is_bounded (P : Polytope A) : poly_bounded P.1
  := ⟨ P, subset_refl P.set ⟩

def Polytope.vertices' (P : Polytope A) : Set A :=
  ⋂₀ { V : Set A | P = convex_hull V }

theorem Polytope.vertices'_is_finite (P : Polytope A) : P.vertices'.Finite := by
  let ⟨ S, V, h_fin, h_S ⟩ := P
  apply Set.Finite.subset h_fin
  apply Set.sInter_subset_of_mem
  exact h_S

def Polytope.vertices (P : Polytope A) : Finset A :=
  P.vertices'_is_finite.toFinset

theorem empty_is_polytope (A : Type*) [AffineSpace V A]
  : Set.is_polytope (∅ : Set A)
  := ⟨ ∅, Set.finite_empty, eq_comm.mp (convex_hull.of_empty_is_empty A) ⟩

def Polytope.empty (A : Type*) [AffineSpace V A] : Polytope A
  := ⟨ ∅, empty_is_polytope A ⟩

theorem point_is_polytope (x : A) : Set.is_polytope {x} := by
  use {x}; simp
  exact (convex_hull.of_point_is_point x).symm

def Polytope.from_point (x : A) : Polytope A := ⟨ {x}, point_is_polytope _ ⟩

def Polytope.affine_span (P : Polytope A) := affineSpan 𝕜 P.1

def Polytope.full_dimension (P : Polytope A) := P.affine_span = ⊤

/-- The affine span of a polytope is of finite dimension. -/
theorem Polytope.finite_dim' (P : Polytope A)
    : FiniteDimensional 𝕜 (P.affine_span.direction) := by
sorry

/-- The ambient space of a full-dimensional polytope is of finite dimension. -/
theorem Polytope.finite_dim (P : Polytope A) (h_fd : P.full_dimension)
    : FiniteDimensional 𝕜 V := by
  let ⟨ S, vert, h_fin, h_set ⟩ := P
  unfold Polytope.full_dimension at h_fd
  unfold Polytope.affine_span at h_fd
  simp at h_fd
  rw [h_set, ←convex_hull.same_affine_span] at h_fd
  --exact finiteDimensional_direction_affineSpan_of_finite h_fd
  sorry

-- theorem ambient_is_polytope_iff_dim_zero (A : Type*) [AffineSpace V A]
--   : (Set.univ : Set A).is_polytope ↔ (Module.rank A) = 0 := sorry

/-- Every subset of a 0-dimensional affine space is a polytope. -/
theorem AffineSpace.subset_of_dim_zero_is_polytope [FiniteDimensional V] (h_dim : AffineSpace.dim A = 0)
    : ∀ S : Set A, S.is_polytope := by
  intro S
  apply AffineSpace.dim_zero_is_subsingleton at h_dim
  cases Set.Subsingleton.eq_empty_or_singleton S.subsingleton_of_subsingleton
  case inl hl => -- S = ∅
    rw [hl]
    exact empty_is_polytope A
  case inr hr => -- S = {x}
    let ⟨ x, hx ⟩ := hr
    rw [hx]
    exact point_is_polytope x

theorem Polytope.is_convex_hull_of_vertices (P : Polytope A)
: P.1 = convex_hull P.vertices := by
  let ⟨ S, V, h_fin, h_S ⟩ := P
  sorry
