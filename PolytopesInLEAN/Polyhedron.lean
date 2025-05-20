
import PolytopesInLEAN.Aux_Finset

import PolytopesInLEAN.Halfspace
import PolytopesInLEAN.Hyperplane
import PolytopesInLEAN.Ray

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

/-- A `Polyhedron` is usually defined as the intersection of finitely many halfspaces.
  For technical reasons they are here defined as intersection of finitely many primspaces. -/
abbrev Set.is_polyhedron (S : Set A) :=
  ∃ Ps : Finset (Primspace A), S = ⋂₀ Ps

/- NOTE: The empty polytope in 0-dimensional affine space is not an intersection
  of halfspaces. This is why the following definition requires `Nontrivial A`.-/
abbrev Set.is_polyhedron' (S : Set A) [Nontrivial A] :=
  ∃ Ps : Finset (Halfspace A), S = ⋂₀ Ps

structure Polyhedron (A : Type*) [AffineSpace V A] where
  set : Set A
  is : set.is_polyhedron

def Polyhedron.from_primspaces (S : Finset (Primspace A)) : Polyhedron A
  := ⟨ ⋂₀ S, S, rfl ⟩

instance : Coe (Polyhedron A) (Set A)
  := ⟨ Polyhedron.set ⟩
instance : Coe (Set (Polyhedron A)) (Set (Set A))
  := ⟨ Set.image Polyhedron.set ⟩
instance : Coe (Finset (Polyhedron A)) (Finset (Set A))
  := ⟨ Finset.image Polyhedron.set ⟩

-- section SetLike

--   instance : SetLike (Polyhedron A) A where
--     coe := Polyhedron.set
--     coe_injective' := fun S₁ S₂ _ => by cases S₁; cases S₂; congr

--   @[simp] lemma mem_carrier {S : Polyhedron A} {x : A}
--     : x ∈ S.set ↔ x ∈ (S : Set A) := Iff.rfl

--   @[ext] theorem ext {S T : Polyhedron A} (h : ∀ x, x ∈ S ↔ x ∈ T) : S = T := SetLike.ext h

-- end SetLike

theorem Primspace.is_polyhedron (P : Primspace A) : (P : Set A).is_polyhedron
  := ⟨ {P}, by simp only [Finset.coe_singleton, Set.image_singleton, Set.sInter_singleton] ⟩

-- theorem Polyhedron.primspace_same_set (P : Primspace A) : (P : Set A) = from_primspaces {P} := by
--   unfold from_primspaces
--   simp only [Finset.coe_singleton, Set.image_singleton, Set.sInter_singleton]

theorem ambient_is_polyhedron (A : Type*) [AffineSpace V A]
: Set.is_polyhedron (Set.univ : Set A)
  := ⟨ ∅, by simp only [Finset.coe_empty, Set.image_empty, Set.sInter_empty] ⟩

/-- The ambient space as a polyhedron. -/
def Polyhedron.ambient (A : Type*) [AffineSpace V A] : Polyhedron A
  := ⟨ Set.univ, ambient_is_polyhedron A ⟩


/-- The empty set is a polyhedron -/
theorem empty_is_polyhedron (A : Type*) [AffineSpace V A]
    : Set.is_polyhedron (∅ : Set A) := by
  use { Primspace.Empty A }
  simp only [Finset.coe_singleton, Set.image_singleton, Set.sInter_singleton]

def Polyhedron.Empty (A : Type*) [AffineSpace V A] : Polyhedron A
  := ⟨ ∅, empty_is_polyhedron A ⟩


theorem AffineSubspace.is_polyhedron (E : AffineSubspace 𝕜 A)
    : Set.is_polyhedron (E : Set A) := by
  sorry

def AffineSubspace.to_Polyhedron (E : AffineSubspace 𝕜 A) : Polyhedron A
  := ⟨ E, E.is_polyhedron ⟩


namespace Polyhedron /- intersection -/

  open Classical

  /-- Intersection of two polyhedra is a polyhedron. -/
  theorem inter_is_polyhedron (P1 P2 : Polyhedron A)
  : Set.is_polyhedron (P1 ∩ P2 : Set A) := by
    let ⟨_, Ps1, h_S1⟩ := P1
    let ⟨_, Ps2, h_S2⟩ := P2
    use (Ps1 ∪ Ps2)
    dsimp only
    rw [h_S1, h_S2]
    rw [←Set.sInter_union]
    rw [←Set.image_union]
    simp only [Set.sInter_image, Set.mem_union, Finset.mem_coe, Finset.coe_union]

  def inter (P1 P2 : Polyhedron A) : Polyhedron A
    := ⟨ _, inter_is_polyhedron P1 P2 ⟩

  instance : Inter (Polyhedron A) := ⟨ inter ⟩

  /-- The intersection of finitely many polyhedra is a polyhedron. -/
  /- NOTE: currently we are using the axiom of choice to select a set of defining
    halfspaces for each polyhedron. Later we can replace this by choosing a
    canonical set of halfspaces, namely, facet defining halfspaces. -/
  theorem sInter_is_polyhedron (polys : Finset (Polyhedron A))
      : Set.is_polyhedron (⋂₀ polys : Set A) := by
    have ⟨ f, hf ⟩ := axiomOfChoice (is (A := A))
    use ⋃₀ᶠ (f ''ᶠ polys)
    rw [funext hf]
    simp only [Set.sInter_image, Finset.mem_coe, Finset.coe_biUnion, Finset.coe_image, Set.mem_image,
      id_eq, Set.iUnion_exists, Set.biUnion_and', Set.iUnion_iUnion_eq_right, Set.mem_iUnion,
      exists_prop, Set.iInter_exists, Set.biInter_and']

  /- A version without explicit use of choice (it is still used as an axiom). -/
  theorem sInter_is_polyhedron' (polys : Finset (Polyhedron A))
      : Set.is_polyhedron (⋂₀ polys : Set A) := by
    induction polys using Finset.induction_on
    case empty =>
      simp only [Finset.coe_empty, Set.image_empty, Set.sInter_empty]
      exact ambient_is_polyhedron A
    case insert P _ _ hInt =>
      simp only [Finset.coe_insert, Set.sInter_image, Set.mem_insert_iff, Finset.mem_coe,
        Set.iInter_iInter_eq_or_left]
      simp only [Set.sInter_image, Finset.mem_coe] at hInt
      exact (inter_is_polyhedron P ⟨_, hInt⟩)

  def sInter (polys : Finset (Polyhedron A)) : Polyhedron A
    := ⟨ _, sInter_is_polyhedron polys ⟩

  theorem is_inter_of_halfspaces (P : Polyhedron A) [Nontrivial A]
      : ∃ Hs : Finset (Halfspace A), (P : Set A) = ⋂₀ Hs := by
    let ⟨ S, Ps, h_S ⟩ := P
    have ⟨ f, hf ⟩ := axiomOfChoice (Primspace.is_inter_of_halspaces (A := A) ·)
    use ⋃₀ᶠ (f ''ᶠ Ps)
    dsimp only; rw [h_S]
    rw [funext hf]
    simp only [Set.sInter_image, Finset.mem_coe, Finset.coe_biUnion, Finset.coe_image, Set.mem_image,
      id_eq, Set.iUnion_exists, Set.biUnion_and', Set.iUnion_iUnion_eq_right, Set.mem_iUnion,
      exists_prop, Set.iInter_exists, Set.biInter_and']

  theorem inter_of_halfspaces_iff (S : Set A) [Nontrivial A]
      : S.is_polyhedron ↔ ∃ Hs : Finset (Halfspace A), S = ⋂₀ Hs := by
    constructor
    exact (is_inter_of_halfspaces ⟨S,·⟩)
    {
      intro h
      let ⟨ Hs, h_Hs ⟩ := h
      use (Halfspace.to_primspace ''ᶠ Hs)
      simp only [Finset.coe_image, Set.sInter_image, Set.mem_image, Finset.mem_coe,
        Set.iInter_exists, Set.biInter_and', Set.iInter_iInter_eq_right]
      simp only [Set.sInter_image, Finset.mem_coe] at h_Hs
      exact h_Hs
    }

  theorem inter_of_halfspaces_iff' {S : Set A} (h : S.Nonempty)
      : S.is_polyhedron ↔ ∃ Hs : Finset (Halfspace A), S = ⋂₀ Hs := by
    sorry

end Polyhedron


theorem Hyperplane.is_polyhedron (H : Hyperplane A)
    : Set.is_polyhedron (H : Set A) := by
  let ⟨ H1, H2, hH ⟩ := H.is_inter_of_two_halfspaces
  use { H1.to_primspace, H2.to_primspace }
  simp only [Finset.coe_insert, Finset.coe_singleton, Set.sInter_image, Set.mem_insert_iff,
    Set.mem_singleton_iff, Set.iInter_iInter_eq_or_left, Set.iInter_iInter_eq_left]
  exact hH

def Hyperplane.to_polyhedron (H : Hyperplane A) : Polyhedron A
  := ⟨ _, H.is_polyhedron ⟩

def Polyhedron.from_halfspaces (Hs : Finset (Halfspace A)) : Polyhedron A
  := ⟨ _, (↑) ''ᶠ Hs, by
    simp only [Set.sInter_image, Finset.mem_coe, Finset.coe_image, Set.mem_image, Set.iInter_exists,
      Set.biInter_and', Set.iInter_iInter_eq_right]
    rfl ⟩



theorem Polyhedron.subspace_restriction_is_polyhedron (P : Polyhedron A) (E : AffineSubspace 𝕜 A) [Nonempty E]
    : Set.is_polyhedron (P ∩ᵣ E) := by
  let ⟨S, prims, h_S⟩ := P
  use (·.restrict_to_subspace E) ''ᶠ prims
  dsimp only; rw [h_S]
  unfold Primspace.restrict_to_subspace
  unfold AffineSubspace.restr
  apply Set.ext
  simp only [Set.sInter_image, Finset.mem_coe, Set.mem_iInter, Set.mem_setOf_eq, Finset.coe_image,
    Set.mem_image, Set.iInter_exists, Set.biInter_and', Set.iInter_iInter_eq_right, implies_true]



def Finset.Primspace.irredundant (Ps : Finset (Primspace A))
  := ∀ Ps' ⊂ Ps, (⋂₀ Ps : Set A) ≠ ⋂₀ Ps'



namespace Polyhedron -- Dimension

  section Dimension

  open Cardinal

  abbrev affineSpan (P : Polyhedron A) : AffineSubspace 𝕜 A
    := _root_.affineSpan 𝕜 P

  abbrev cdim (P : Polyhedron A) : Cardinal := P.affineSpan.cdim
  abbrev  dim (P : Polyhedron A) : ℕ := P.affineSpan.dim
  abbrev sdim (P : Polyhedron A) : ℤ := P.affineSpan.sdim

  abbrev codim (P : Polyhedron A) [AffineSpace.FiniteDimensional A] : ℕ
    := P.affineSpan.codim

  abbrev FiniteDimensional (P : Polyhedron A)
    := P.affineSpan.FiniteDimensional

  abbrev nonempty (P : Polyhedron A) := (P : Set A).Nonempty

  def in_affineSpan (P : Polyhedron A) [Nonempty P.affineSpan]
      : Polyhedron (P.affineSpan) := ⟨ _, subspace_restriction_is_polyhedron P P.affineSpan ⟩


  -- protected lemma few_primspaces_ray_unbounded [AffineSpace.FiniteDimensional A]
  --   {Ps : Finset (Primspace A)} (h : #Ps < AffineSpace.dim A)
  --     : ¬Set.ray_bounded (from_primspaces Ps : Set A) := by
  --   sorry

  protected lemma inf_dim_nonempty_is_ray_unbounded
    (P : Polyhedron A) (h : ¬AffineSpace.FiniteDimensional A)
      : ¬Set.ray_bounded (P : Set A) := by
    sorry

  protected lemma nonempty_ray_unbounded_impl_finite_dim_ambient
    {P : Polyhedron A} (h_ne : P.nonempty) (h_rb : (P : Set A).ray_bounded)
      : AffineSpace.FiniteDimensional A := by
    by_contra h

    sorry

  /-- If a polyhedron is ray-bounded then it is of finite dimension. -/
  theorem ray_bounded_impl_finite_dim {P : Polyhedron A} (h_bd : Set.ray_bounded P.set)
      : FiniteDimensional P := by
    -- by_contra h_dim
    -- unfold FiniteDimensional at h_dim
    -- let ⟨ S, prims, h_Sdef ⟩ := P
    -- let HSs := { Pr ∈ prims | Set.is_halfspace Pr.1 }
    -- let bnds := (fun Pr : Primspace A => Pr.boundary_hyperplane) '' HSs
    -- let modules := (fun Hp : hyperplane A => Ho.to_AffineSpace.direction) '' bnds
    sorry

    theorem finite_dim_impl_finite_dim_ambient {P : Polyhedron A} [FiniteDimensional P]
      : AffineSpace.FiniteDimensional A := sorry

  end Dimension

end Polyhedron
