
import PolytopesInLEAN.Primspace
import PolytopesInLEAN.Ray

variable {𝕜 : Type*} [LinearOrderedField 𝕜]
variable {V : Type*} [VectorSpace 𝕜 V]
variable {A : Type*} [AffineSpace V A]

noncomputable section

attribute [local instance] Classical.propDecidable

-- Halfspaces --

-- Can also serve as an oriented hyperplane

open Function

abbrev AffineMap.halfspace_carrier (f : A →ᵃ[𝕜] 𝕜) : Set A := f ⁻¹' (Set.Ici 0)

def Set.is_halfspace (S : Set A)
  := ∃ f : A →ᵃ[𝕜] 𝕜, is_nonconst f ∧ S = f.halfspace_carrier
  -- := ∃ f : A →ᵃ[𝕜] 𝕜, is_nonconst f ∧ S = f ⁻¹' (Ici 0)

structure Halfspace (A : Type*) [AffineSpace V A] where
  set : Set A
  is : set.is_halfspace
-- abbrev Halfspace (A : Type*) [AffineSpace V A] := { S : Set A // S.is_halfspace }
instance : Coe (Halfspace A) (Set A) := ⟨ Halfspace.set ⟩
instance : Coe (Set (Halfspace A)) (Set (Set A)) := ⟨ Set.image Halfspace.set ⟩


namespace Halfspace

  /-- A `Halfspace` constructed from a given affine map. -/
  abbrev from_map {f : A →ᵃ[𝕜] 𝕜} (h : is_nonconst f) : Halfspace A :=
    ⟨ _, f, ⟨ h, rfl ⟩  ⟩

  /- EXPERIMENTS -/

  /- I don't think that the following definitions are a good idea.
    The problem is not the use of `Choice`, but that it is very hard
    to use them properly. For example, one cannot prove that the maps
    obtained by `Halfspace.map` from two identical halfspaces are the
    same map (see below). -/

  def map (H : Halfspace A) : A →ᵃ[𝕜] 𝕜
    := Classical.choose H.is
  protected def map_spec (H : Halfspace A)
    := Classical.choose_spec H.is
  def map_nonconst (H : Halfspace A) : is_nonconst H.map
    := H.map_spec.1
  def map_def (H : Halfspace A) : H = H.map.halfspace_carrier
    := H.map_spec.2

  theorem from_map_map {f : A →ᵃ[𝕜] 𝕜} (h : is_nonconst f)
      : (from_map h).map = f := by
    unfold from_map
    /- I think this cannot be proven. It is not clear that the axiom of choice
      gives back the same map that I used to construct the halfspace. -/
    sorry

end Halfspace


namespace Halfspace

  theorem nonempty' (H : Halfspace A) : Set.Nonempty (H : Set A) := by
    let ⟨ S, f, h_fnc, h_f ⟩ := H
    apply AffineMap.non_const_form_is_surj at h_fnc
    let ⟨ x, hx ⟩ := h_fnc 0
    use x
    simp only [h_f, Set.mem_preimage, hx, Set.mem_Ici, le_refl]

  theorem nonempty (H : Halfspace A) : (H : Set A) ≠ ∅
    := Set.nonempty_iff_ne_empty.mp H.nonempty'

  theorem proper (H : Halfspace A) : (H : Set A) ≠ Set.univ := by
    let ⟨ S, f, h_fnc, h_f ⟩ := H
    apply AffineMap.non_const_form_is_surj at h_fnc
    let ⟨ x, hx ⟩ := h_fnc 0
    simp only [h_f, ne_eq, Set.preimage_eq_univ_iff]
    sorry

end Halfspace


theorem Halfspace.is_primspace (H : Halfspace A) : (H : Set A).is_primspace := by
  let ⟨_, f, _, _⟩ := H; use f

def Primspace.from_halfspace (H : Halfspace A) : Primspace A
   := ⟨ H, H.is_primspace ⟩
def Halfspace.to_primspace (H : Halfspace A) : Primspace A
   := ⟨ H, H.is_primspace ⟩
instance : Coe (Halfspace A) (Primspace A) := ⟨ Halfspace.to_primspace ⟩

def Halfspace.coe_primspace (H : Halfspace A)
  : (H : Set A) = (H.to_primspace : Set A) := rfl

/-- A Primspace is either empty, the full space, or a Halfspace. -/
theorem Primspace.cases (P : Primspace A)
    : (P : Set A) = ∅
    ∨ (P : Set A) = Set.univ
    ∨ (P : Set A).is_halfspace := by
  let ⟨ S, f, hf ⟩ := P
  dsimp only
  by_cases hc : Function.is_const f
  let ⟨q, hw⟩ := Function.is_const_impl' hc
  rw [hf, hw]
  by_cases h_in : q ∈ Set.Ici 0
  -- case 1.1: f is const, image in [0,inf)
  right; left
  exact Set.preimage_const_of_mem h_in
  -- case 1.2: f is const, image not in [0,inf)
  left
  exact Set.preimage_const_of_not_mem h_in
  -- case 2: f is not const
  right; right
  use f

theorem Halfspace.to_primspace_nontrivial (H : Halfspace A)
    : H.to_primspace.nontrivial := by
  rcases H.to_primspace.cases with h | h | h
  case inl h => exfalso; exact H.nonempty h
  case inr.inl h => exfalso; exact H.proper h
  case inr.inr h => exact ⟨ H.nonempty, H.proper ⟩

theorem Primspace.nontrivial_is_halfspace {P : Primspace A} (hn : P.nontrivial)
    : (P : Set A).is_halfspace := by
  rcases P.cases with h | h | h
  case inl h => exfalso; exact hn.1 h
  case inr.inl h => exfalso; exact hn.2 h
  case inr.inr h => exact h

def Halfspace.from_primspace {P : Primspace A} (hn : P.nontrivial)
  : Halfspace A := ⟨ _, P.nontrivial_is_halfspace hn ⟩

instance [Nontrivial A] : Nonempty (Halfspace A)
  := ⟨ Halfspace.from_map (Classical.choose_spec (AffineMap.exists_non_const A 𝕜)) ⟩



theorem Halfspace.exists_halfspace_empty_inter (H : Halfspace A)
    : ∃ H' : Halfspace A, (H ∩ H' : Set A) = ∅ := by
  let ⟨ _, f1, h1, h1' ⟩ := H
  --
  let f2 := -f1 - AffineMap.const 𝕜 A 1
  have h2 : ¬is_const f2 := by -- TODO write lemmas for is_const to shorten this part
    unfold is_const
    unfold is_nonconst is_const at h1
    push_neg
    push_neg at h1
    let ⟨ x, y, h ⟩ := h1
    use x, y
    unfold f2
    simp only [AffineMap.coe_sub, AffineMap.coe_neg, AffineMap.coe_const, const_one, Pi.sub_apply,
      Pi.neg_apply, Pi.one_apply, ne_eq, sub_left_inj, neg_inj]
    exact h
  let H' := Halfspace.from_map (f := f2) h2
  --
  use H'
  apply Set.eq_empty_of_subset_empty
  dsimp
  rw [h1']
  rw [Set.subset_def]
  intro x
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_Ici, Set.mem_empty_iff_false, imp_false,
    not_and, not_le]
  intro h
  unfold f2
  simp only [AffineMap.coe_sub, AffineMap.coe_neg, AffineMap.coe_const, const_one, Pi.sub_apply,
    Pi.neg_apply, Pi.one_apply, sub_neg]
  linarith [h]

lemma Halfspace.exists_empty_inter (A : Type*) [AffineSpace V A] [Nontrivial A]
    : ∃ H1 H2 : Halfspace A, (H1 ∩ H2 : Set A) = ∅ := by
  have H1 := Classical.arbitrary (Halfspace A)
  let ⟨ H2, h ⟩ := exists_halfspace_empty_inter H1
  use H1, H2

lemma Primspace.is_inter_of_halspaces' {P : Primspace A} (h_ne : (P : Set A) ≠ ∅)
    : ∃ Hs : Finset (Halfspace A), (P : Set A) = ⋂₀ Hs := by
  cases Primspace.cases P
  case inl h => exfalso; exact h_ne h
  case inr h =>
    cases h
    case inl h =>
      use ∅
      rw [Finset.coe_empty, Set.image_empty, Set.sInter_empty, h]
    case inr h =>
      use {⟨ P, h ⟩}
      simp only [Finset.coe_singleton, Set.image_singleton, Set.sInter_singleton]

lemma Primspace.is_inter_of_halspaces (P : Primspace A) [Nontrivial A]
    : ∃ Hs : Finset (Halfspace A), (P : Set A) = ⋂₀ Hs := by
  by_cases (P : Set A) = ∅
  case pos h =>
    let ⟨ H1, H2, hH ⟩ := Halfspace.exists_empty_inter A
    use {H1, H2}
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.sInter_image, Set.mem_insert_iff,
      Set.mem_singleton_iff, Set.iInter_iInter_eq_or_left, Set.iInter_iInter_eq_left]
    rw [hH, h]
  case neg h => exact Primspace.is_inter_of_halspaces' h



/- Proving equiavlence of halfspaces is not easy, which is why I am considering
  a different approach via suitable quotient constructions. -/

namespace Halfspace

  lemma id_iff {f g : A →ᵃ[𝕜] 𝕜} (hf : ¬is_const f) (hg : ¬is_const g)
      : from_map hf = from_map hg ↔ ∃ c : 𝕜, c > 0 ∧ f = c • g
    := by sorry

  lemma id_iff' (H H' : Halfspace A)
      : H = H' ↔ ∃ f g : A →ᵃ[𝕜] 𝕜, ¬is_const f ∧ ¬is_const g ∧ ∃ c : 𝕜, c > 0 ∧ f = c • g
    := by sorry

end Halfspace



namespace Halfspace -- affine transformations

  section

    open Primspace

    theorem affine_equiv_is_halfspace (H : Halfspace A) (φ : A ≃ᵃ[𝕜] A)
        : (φ '' H).is_halfspace := nontrivial_is_halfspace
      (affine_trafo_of_nontrivial_is_nontrivial H.to_primspace_nontrivial)

  end

  abbrev transform (H : Halfspace A) (φ : A ≃ᵃ[𝕜] A) : Halfspace A
    := ⟨ _, H.affine_equiv_is_halfspace φ ⟩

  abbrev translate (H : Halfspace A) (v : V) : Halfspace A
    := H.transform (AffineEquiv.Translation A v)

end Halfspace



/- It appears necessary to talk about parallel halfspaces. There are currently
  major problems with this implementation. -/

namespace Halfspace -- parallels

  def is_parallel (H H' : Halfspace A)
    := (H ∩ H' : Set A).is_halfspace

  def is_antiparallel (H H' : Halfspace A)
    := ∃ H'' : Halfspace A, H'.is_parallel H'' ∧ (H ∩ H'' : Set A) = ∅

  def parallels (H : Halfspace A)
    := { H' : Halfspace A // H.is_parallel H' }

  theorem is_parallel_comm {H H' : Halfspace A} (h : H.is_parallel H') : H'.is_parallel H := by
    unfold is_parallel
    rw [Set.inter_comm]
    exact h

  theorem is_parallel_refl (H : Halfspace A) : H.is_parallel H := by
    unfold is_parallel
    rw [Set.inter_self]
    exact H.is

  theorem is_parallel_subset_cases {H H' : Halfspace A} (h : H.is_parallel H')
      : (H : Set A) ⊆ H' ∨ (H' : Set A) ⊆ H := by
    sorry

  theorem is_parallel_trans {H H' H'' : Halfspace A}  (h : H.is_parallel H') (h' : H'.is_parallel H'')
      : H.is_parallel H'' := by
    unfold is_parallel at *
    sorry

  -- TODO:
  -- define symm, trans, refl for parallel halfspaces
  -- better: define an equivalence relation structure

  theorem translate_is_parallel (H : Halfspace A) (v : V)
      : H.is_parallel (H.translate v) := by
    unfold is_parallel translate
    unfold AffineEquiv.Translation
    unfold Set.is_halfspace
    dsimp
    -- ...
    sorry

  theorem inter_of_parallel_is_halfspace {H H' : Halfspace A} (h : H.is_parallel H')
      : (H ∩ H' : Set A).is_halfspace := h

  theorem union_of_parallel_is_halfspace {H H' : Halfspace A} (h : H.is_parallel H')
      : (H ∪ H' : Set A).is_halfspace := by
    unfold Set.is_halfspace
    sorry

end Halfspace



namespace Halfspace -- further parallel experiments

  variable {H0 H1 : Halfspace A} (h : H0.is_parallel H1)

  def parallel_coord (H : Halfspace A) : 𝕜 := sorry
  def parallel_locate (k : 𝕜) : Halfspace A := sorry

  theorem parallel_locate_def (k : 𝕜) : H0.is_parallel (parallel_locate k) := sorry

  def Halfspace.parallels_equiv_k {H0 H1 : Halfspace A} (h : H0.is_parallel H1)
      : parallels H0 ≃ 𝕜 where
        toFun := sorry
        invFun := sorry
        left_inv := sorry
        right_inv := sorry

end Halfspace

/- The eventual goas was to show that the set of parallels of a halfspace
  carries the structure of a vector space. There might be easier ways to
  to achieve what I initially had in mind with this. -/

instance (H : Halfspace A) : VectorSpace 𝕜 (Halfspace.parallels H) := sorry





--def Halfspace.boundary (H: Halfspace A) Set A := (Classical.choose H.2) ⁻¹' {(0 : 𝕜)}

theorem Halfspace.ray_unbounded (H : Halfspace A) : ¬Set.ray_bounded H.1 := by
  unfold Set.ray_bounded
  push_neg
  let ⟨ S, f, h_nc, h_f ⟩ := H
  -- TODO: use that f is not const, hence maps surjectively to 𝕜, then the preimage of Set.Ici is a ray.
  sorry
