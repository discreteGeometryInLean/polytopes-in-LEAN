
import PolytopesInLEAN.Aux_General

variable {𝕜 : Type*} [LinearOrderedField 𝕜]
variable {V : Type*} [VectorSpace 𝕜 V]
variable {A : Type*} [AffineSpace V A]

-- Convexity and convex hull --

/- There is currently no implementation of convexity for affine spaces.
  For this reason we have to implement our own version for now. -/

def Set.is_convex (S : Set A)
  := ∀ x y : A, x ∈ S ∧ y ∈ S → ∀ t : 𝕜, 0 ≤ t ∧ t ≤ 1 → t • (y -ᵥ x) +ᵥ x ∈ S

theorem AffineSpace.empty_is_convex (A : Type*) [AffineSpace V A]
: Set.is_convex (∅ : Set A) := by
  unfold Set.is_convex; simp

theorem AffineSpace.ambient_is_convex (A : Type*) [AffineSpace V A]
: Set.is_convex (Set.univ : Set A) := by
  unfold Set.is_convex; simp

theorem AffineSpace.subspace_is_convex (E : AffineSubspace 𝕜 A)
    : Set.is_convex E.carrier := by
  unfold Set.is_convex
  intro x y
  simp
  intro hx hy _ _ _
  apply E.smul_vsub_vadd_mem
  repeat assumption /- hy hx hx -/

theorem AffineSpace.point_is_convex (x : A) : Set.is_convex {x} := by
  unfold Set.is_convex
  intro x y
  simp
  intro hx hy t ht0 ht1
  rw [hx, hy]
  simp

def convex_hull (S : Set A) : Set A
  := ⋂₀ { T : Set A | T.is_convex ∧ S ⊆ T }

theorem convex_hull.of_set_contains_set (S : Set A) : S ⊆ convex_hull S := by
  unfold convex_hull; simp

theorem convex_hull.is_convex (S : Set A) : (convex_hull S).is_convex := by
  intro x y ⟨ hx, hy ⟩ t ht
  unfold convex_hull
  rw [Set.mem_sInter]
  intro T hT
  have h : convex_hull S ⊆ T := by
    apply Set.sInter_subset_of_mem
    simp [hT]
  have hx' : x ∈ T := Set.mem_of_mem_of_subset hx h
  have hy' : y ∈ T := Set.mem_of_mem_of_subset hy h
  apply hT.1 x y ⟨ hx', hy' ⟩ t ht

-- theorem convex_hull_of_compact_is_compact (S : Set A)
--   : S.IsCompact → (convex_hull S).IsCompact := by
--   sorry

/-- Convex hull of a convex set is the set itself. -/
theorem convex_hull.of_convex_is_same (S : Set A) (hS : S.is_convex)
    : convex_hull S = S := by
  have h : S ∈ {T | T.is_convex ∧ S ⊆ T} := by
    simp; exact hS
  have h2 : ⋂₀ {T | T.is_convex ∧ S ⊆ T} ⊆ S :=
    Set.sInter_subset_of_mem h
  have h3 : S ⊆ ⋂₀ {T | T.is_convex ∧ S ⊆ T} := by simp
  exact subset_antisymm h2 h3

theorem convex_hull.of_empty_is_empty (A : Type*) [AffineSpace V A]
: convex_hull ∅ = (∅ : Set A) :=
  convex_hull.of_convex_is_same ∅ (AffineSpace.empty_is_convex A)

theorem convex_hull.of_ambient_is_ambient (A : Type*) [AffineSpace V A]
: convex_hull Set.univ = (Set.univ : Set A) :=
  convex_hull.of_convex_is_same Set.univ (AffineSpace.ambient_is_convex A)

theorem convex_hull.of_point_is_point (x : A) : convex_hull {x} = {x} :=
  convex_hull.of_convex_is_same {x} (AffineSpace.point_is_convex x)

theorem convex_hull.of_convex_hull_is_convex_hull (S : Set A)
    : convex_hull (convex_hull S) = convex_hull S :=
  convex_hull.of_convex_is_same (convex_hull S) (convex_hull.is_convex S)

theorem convex_hull.of_subspace_is_same (E : AffineSubspace 𝕜 A)
    : convex_hull E = E.carrier :=
  convex_hull.of_convex_is_same E.carrier (AffineSpace.subspace_is_convex E)

theorem convex_hull.same_affine_span (S : Set A)
: affineSpan 𝕜 S = affineSpan 𝕜 (convex_hull S) := by
  sorry


-- theorem convex_hull.has_convex_coordinates (S : Set A) [Fintype S] (x : A) (h : x ∈ convex_hull S)
--   : ∃ f : S → 𝕜, (∀ s : S, f s ≥ 0 ∧ f s ≤ 1)
--     ∧ ∑ (s : S), f s = 1
--     ∧ ∑ (s : S), (f s) • (s  = x

-- theorem convex_hull.finite_dim_iff (S : Set A)
-- : FiniteDimensional 𝕜 () ↔
