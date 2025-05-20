
import PolytopesInLEAN.Aux_General

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

-- notation "[0,∞)" => (Set.Ici 0)

-- Primspace --

/- `Primspace`s have the advantage over general halfspaces that the intersection of a
  Primspace with an affine subspace is always a `Primspace` in this affine subspace. -/

def Set.is_primspace (S : Set A)
  := ∃ f : A →ᵃ[𝕜] 𝕜, S = f ⁻¹' (Ici 0)

/-- A `Primspace` or 'primitive space' is either a halfspace, empty or the full space. -/
structure Primspace (A : Type*) [AffineSpace V A] where
  set : Set A
  is : set.is_primspace
instance : Coe (Primspace A) (Set A) := ⟨ Primspace.set ⟩
instance : Coe (Set (Primspace A)) (Set (Set A)) := ⟨ Set.image Primspace.set ⟩
instance : Coe (Finset (Primspace A)) (Finset (Set A)) := ⟨ Finset.image Primspace.set ⟩

abbrev Primspace.from_map (f : A →ᵃ[𝕜] 𝕜) : Primspace A :=
  ⟨ f ⁻¹' (Set.Ici 0), f, rfl ⟩

theorem AffineSpace.ambient_is_primspace (A : Type*) [AffineSpace V A]
    : Set.is_primspace (Set.univ : Set A) := by
  use 0
  rw [AffineMap.coe_zero]
  have h : (0 : A → 𝕜) = (fun _ => (0 : 𝕜)) := by
    apply funext
    intro _; rw [Pi.zero_apply]
  rw [h, Set.preimage_const_of_mem]
  rw [Set.mem_Ici]

theorem AffineSpace.empty_is_primspace (A : Type*) [AffineSpace V A]
    : Set.is_primspace (∅ : Set A) := by
  use AffineMap.const 𝕜 A (-1)
  simp
  unfold Function.const
  rw [Set.preimage_const_of_not_mem]
  simp

namespace Primspace

  abbrev Ambient (A : Type*) [AffineSpace V A]
    : Primspace A := ⟨Set.univ, AffineSpace.ambient_is_primspace A⟩

  abbrev ambient (P : Primspace A) := (P : Set A) = Set.univ
  abbrev proper (P : Primspace A) := (P : Set A) ≠ Set.univ

  abbrev Empty (A : Type*) [AffineSpace V A]
    : Primspace A := ⟨∅, AffineSpace.empty_is_primspace A⟩

  abbrev empty (P : Primspace A) := (P : Set A) = ∅
  abbrev nonempty (P : Primspace A) := (P : Set A) ≠ ∅

  abbrev trivial (P : Primspace A) := P.empty ∨ P.ambient
  abbrev nontrivial (P : Primspace A) := P.nonempty ∧ P.proper

end Primspace

namespace Primspace

  /-- The restriction of a Primspace to an affine subspace is a Primspace of that
  subspace (but not necessarily of the ambient space). -/
  theorem subspace_restriction_is_primspace (P : Primspace A)
    (E : AffineSubspace 𝕜 A) [Nonempty E] : Set.is_primspace (P ∩ᵣ E) := by
    let ⟨S, f, hf⟩ := P
    exact ⟨ f.restrict_dom E, AffineMap.preimage_restrict_dom hf E ⟩

  def restrict_to_subspace (P : Primspace A) (E : AffineSubspace 𝕜 A) [Nonempty E]
    : Primspace E := ⟨ P ∩ᵣ E, P.subspace_restriction_is_primspace E ⟩

end Primspace

theorem AffineSubspace.exists_projection (E : AffineSubspace 𝕜 A) [Nonempty E]
    : ∃f : A →ᵃ[𝕜] E, ∀ x ∈ E, f x = x := by
    -- : ∃f : A →ᵃ[𝕜] E, f.restrict_dom E = AffineMap.id 𝕜 E := by
  -- exists_subset_affineIndependent_affineSpan_eq_top
  sorry

namespace Primspace

  /-- A `Primspace` of an affine subspace `E` of `A` is the restriction of some
    `Primspace` of `A`. -/
  theorem extend {E : AffineSubspace 𝕜 A} [Nonempty E] (P : Primspace E)
      : ∃ P' : Primspace A, P = P' ∩ᵣ E := by
    let ⟨ g, h_g ⟩ := E.exists_projection
    let ⟨ S, f, h_f ⟩ := P
    use Primspace.mk _ ( by use f.comp g )
    dsimp only
    rw [h_f]
    unfold AffineSubspace.restr
    unfold Set.Ici
    simp only [Set.preimage_setOf_eq, AffineMap.coe_comp, Function.comp_apply, Set.mem_setOf_eq]
    apply Set.ext
    intro x
    simp only [Set.mem_setOf_eq]
    rw [Subtype.coe_inj.mp (h_g x x.2)]

  def affineSpan (P : Primspace A) := _root_.affineSpan 𝕜 (P : Set A)

  theorem affineSpan_empty_or_ambient (P : Primspace A)
      : P.affineSpan = ⊥ ∨ P.affineSpan = ⊤ := by
    sorry

  theorem finite_dim_iff_ambient_finite_dim (P : Primspace A) (h_ne : (P : Set A) ≠ ∅) :
      (P : Set A).FiniteDimensional ↔ AffineSpace.FiniteDimensional A := by
    sorry

  theorem sInter_finite_dim_iff_ambient_finite_dim (Ps : Finset (Primspace A))
    (h_ne : ∃ P ∈ Ps, (P : Set A) ≠ ∅) :
      (⋂₀ Ps : Set A).FiniteDimensional ↔ AffineSpace.FiniteDimensional A := by
    sorry

end Primspace




theorem Function.image_preimage_is_comp_inv_preimage {α β : Type*} {f : α ≃ α} {g : α → β} {S : Set β} :
    f '' (g ⁻¹' S) = (g ∘ f.invFun) ⁻¹' S := by
  rw [Equiv.invFun_as_coe]
  ext x -- apply Set.ext; intro x
  simp only [Set.mem_image_equiv, Set.mem_preimage, Function.comp_apply]

/-- Translation by a vector `v`. -/
def AffineEquiv.Translation (A : Type*) [AffineSpace V A] (v : V) : A ≃ᵃ[𝕜] A where
  toFun := (v +ᵥ ·)
  invFun := (-v +ᵥ ·)
  left_inv := neg_vadd_vadd v
  right_inv := vadd_neg_vadd v
  linear := LinearEquiv.refl 𝕜 V
  map_vadd' := by
    intro x w
    simp only [Equiv.coe_fn_mk, LinearEquiv.refl_apply]
    rw [←vadd_assoc, ←vadd_comm, vadd_assoc]



namespace Primspace

  /-- An affine transformation of a `Primspace` is a again a `Primspace`. -/
  theorem affine_equiv_is_primspace (P : Primspace A) (φ : A ≃ᵃ[𝕜] A)
      : (φ '' P).is_primspace := by
    let ⟨ S, f, hf ⟩ := P
    use AffineMap.comp f φ.symm
    dsimp only
    rw [hf]
    exact Function.image_preimage_is_comp_inv_preimage

  abbrev transform (P : Primspace A) (φ : A ≃ᵃ[𝕜] A) : Primspace A
    := ⟨ _, P.affine_equiv_is_primspace φ ⟩

  theorem affine_trafo_of_nonempty_is_nonempty {P : Primspace A} {φ : A ≃ᵃ[𝕜] A}
      (hn : P.nonempty) : (P.transform φ).nonempty := by
    simp only [ne_eq, Set.image_eq_empty]
    assumption

  theorem affine_trafo_of_ambient_is_ambient {P : Primspace A} {φ : A ≃ᵃ[𝕜] A}
      (ha : P.ambient) : (P.transform φ).ambient := by
    unfold ambient transform
    simp only [ha, Set.image_univ, AffineEquiv.range_eq]

  theorem affine_trafo_of_proper_is_proper {P : Primspace A} {φ : A ≃ᵃ[𝕜] A}
      (hp : P.proper) : (P.transform φ).proper := by
    simp only [ne_eq]
    push_neg
    unfold proper at hp
    sorry

  theorem affine_trafo_of_nontrivial_is_nontrivial {P : Primspace A} {φ : A ≃ᵃ[𝕜] A}
      (h : P.nontrivial) : (P.transform φ).nontrivial :=
    ⟨ affine_trafo_of_nonempty_is_nonempty h.1, affine_trafo_of_proper_is_proper h.2 ⟩

end Primspace



theorem Primspace.equiv (f g : A →ᵃ[𝕜] 𝕜)
    : from_map f = from_map g ↔ ∃ c : 𝕜, c > 0 ∧ f = c • g := by
  constructor
  --
  simp only [mk.injEq, gt_iff_lt]
  intro h
  sorry
  --
  sorry
