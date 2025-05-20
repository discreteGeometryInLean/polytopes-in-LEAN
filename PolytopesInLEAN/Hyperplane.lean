
import PolytopesInLEAN.Halfspace

noncomputable section

variable {𝕜 : Type*} [LinearOrderedField 𝕜]
variable {V : Type*} [VectorSpace 𝕜 V]
variable {A : Type*} [AffineSpace V A]

-- Hyperplanes --

open Function

abbrev AffineMap.hyperplane_carrier (f : A →ᵃ[𝕜] 𝕜) : Set A := f ⁻¹' {0}

def Set.is_hyperplane (S : Set A)
:= ∃ f : A →ᵃ[𝕜] 𝕜, ¬is_const f ∧ S = f.hyperplane_carrier
-- := ∃ f : A →ᵃ[𝕜] 𝕜, ¬is_const f ∧ S = f ⁻¹' {0}

structure Hyperplane (A : Type*) [AffineSpace V A] where
  set : Set A
  is : set.is_hyperplane
instance : Coe (Hyperplane A) (Set A) := ⟨Hyperplane.set⟩
instance : Coe (Set (Hyperplane A)) (Set (Set A)) := ⟨Set.image Hyperplane.set⟩


namespace Hyperplane -- map

  abbrev from_map {f : A →ᵃ[𝕜] 𝕜} (h : ¬is_const f) : Hyperplane A :=
    ⟨ _, _, ⟨ h, rfl ⟩  ⟩

  /- EXPERIMENTS -/

  /- I don't think that the following definitions are a good idea.
    See corresponding comment for `Halfspace`. -/

  def map (H : Hyperplane A) : A →ᵃ[𝕜] 𝕜
    := Classical.choose H.is
  protected def map_spec (H : Hyperplane A)
    := Classical.choose_spec H.is
  def map_nonconst (H : Hyperplane A) : is_nonconst H.map
    := H.map_spec.1
  def map_def (H : Hyperplane A) : H = H.map.hyperplane_carrier
    := H.map_spec.2

end Hyperplane

/-- A hyplerplane is always nonempty. -/
theorem Hyperplane.nonempty (H : Hyperplane A) : Set.Nonempty (H : Set A) := by
  let ⟨ S, f, h_fnc, h_f ⟩ := H
  apply AffineMap.non_const_form_is_surj at h_fnc
  let ⟨ x, hx ⟩ := h_fnc 0
  use x
  simp only [h_f, Set.mem_preimage, hx, Set.mem_singleton_iff]

theorem Hyperplane.not_univ (H : Hyperplane A) : (H : Set A) ≠ Set.univ := by
  let ⟨ S, f, h_fnc, h_f ⟩ := H
  apply AffineMap.non_const_form_is_surj at h_fnc
  let ⟨ x, hx ⟩ := h_fnc (-1)
  dsimp
  rw [Set.ext_iff]
  push_neg
  use x
  simp [h_f, Set.mem_preimage, hx]

def Hyperplane.get_halfspace (H : Hyperplane A) : Halfspace A
  := Halfspace.from_map H.map_nonconst

/-- A hyplerplane can be written as the intersection of two halfspaces. -/
theorem Hyperplane.is_inter_of_two_halfspaces (H : Hyperplane A)
  : ∃ H1 H2 : Halfspace A, H = (H1 ∩ H2 : Set A) := by
  let ⟨f, h_fnc, hf⟩ := H.2
  let H1_set := f ⁻¹' (Set.Ici 0)
  let H2_set := f ⁻¹' (Set.Iic 0)
  have h_sh1h2 : H = H1_set ∩ H2_set := by
    rw [hf]
    rw [←Set.preimage_inter]
    rw [Set.Ici_inter_Iic_is_singleton]
  have h : f ⁻¹' (Set.Iic 0) = (-f) ⁻¹' (Set.Ici 0) := by
    unfold Set.Ici
    unfold Set.Iic
    simp only [Set.preimage_setOf_eq, AffineMap.coe_neg, Pi.neg_apply, Left.nonneg_neg_iff]
  have h_nfnc : ¬is_const (-f) := by
    apply mt (const_neg_const (f := -f))
    rw [AffineMap.coe_neg, neg_neg]
    exact h_fnc
  use ⟨ H1_set,  f, h_fnc,  by rfl ⟩ -- H1
  use ⟨ H2_set, -f, h_nfnc, by sorry /- rw[←h] -/ ⟩ -- H2


namespace Hyperplane

  def to_AffineSubspace (H : Hyperplane A)
      : AffineSubspace 𝕜 A  where
    carrier := H
    smul_vsub_vadd_mem _ _ _ _ h1 h2 h3 := by
      let ⟨ _, _, _, h_f ⟩ := H
      simp only [h_f, Set.mem_preimage, Set.mem_singleton_iff] at h1 h2 h3
      simp [h_f, h1, h2, h3]

  def to_AffineSubspace' (H : Hyperplane A)
      : AffineSubspace 𝕜 A := affineSpan 𝕜 H

  instance (H : Hyperplane A) : Nonempty H.to_AffineSubspace :=
    Set.Nonempty.to_subtype (nonempty H)

  abbrev cdim (H : Hyperplane A) : Cardinal := H.to_AffineSubspace.cdim
  abbrev  dim (H : Hyperplane A) : ℕ := H.to_AffineSubspace.dim

  abbrev codim (H : Hyperplane A) [AffineSpace.FiniteDimensional A] : ℕ
    := H.to_AffineSubspace.codim

  abbrev FiniteDimensional (H : Hyperplane A)
    := H.to_AffineSubspace.FiniteDimensional
  abbrev InfiniteDimensional (H : Hyperplane A)
    := ¬FiniteDimensional H

  theorem fin_dim_impl_ambient_fin_dim {H : Hyperplane A} (h : H.FiniteDimensional)
      : AffineSpace.FiniteDimensional A := by
    sorry

  theorem ambient_inf_dim_impl_inf_dim (h : AffineSpace.InfiniteDimensional A)
      (H : Hyperplane A) : InfiniteDimensional H := by
    --unfold InfiniteDimensional
    by_contra h
    sorry

end Hyperplane



def Hyperplane.is_parallel (H H' : Hyperplane A)
  := H = H' ∨ (H ∩ H' : Set A) = ∅


lemma Hyperplane.id_iff {f g : A →ᵃ[𝕜] 𝕜} (hf : is_nonconst f) (hg : is_nonconst g)
    : from_map hf = from_map hg ↔ ∃ c : 𝕜, f = c • g := by
    -- : from_map hf = from_map hg ↔ ∃ c : 𝕜, c ≠ 0 ∧ f = c • g := by
  constructor
  {
    intro h
    rw [mk.injEq] at h
    rw [Set.ext_iff] at h
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at h
    have h' : ∃ x, f x ≠ 0 := by
      unfold is_nonconst is_const at hf
      push_neg at hf
      let ⟨ x, y, hxy ⟩ := hf
      by_cases f x = 0
      case neg h => exact ⟨ x, h ⟩
      case pos h => exact ⟨ y, by rw [←h]; exact hxy.symm ⟩
    have ⟨ x, hx ⟩ := h'
    use f x / g x
    -- constructor
    -- {
    --   simp only [ne_eq, div_eq_zero_iff, not_or]
    --   exact ⟨ hx, mt (h x).mpr hx ⟩
    -- }
    {
      apply AffineMap.ext
      intro y
      simp only [AffineMap.coe_smul, Pi.smul_apply, smul_eq_mul]
      ring_nf
      rw [mul_assoc]
      -- IDEA:
      -- if dim A = 0, then x is a basis
      -- if dim A > 1, then choose y so that f y = 0, then x,y are a basis (since f x != 0)
      -- verify the goal for x and y
      -- conclude that f and g are therefore identical
      by_cases Nontrivial A
      case pos h =>
        let h := exists_pair_ne A
        sorry
      case neg h =>
        --let h := exists_pair_ne A
        sorry
    }
  }
  {
    intro hc
    let ⟨ c, hc' ⟩ := hc
    --let ⟨ c, hc, hc' ⟩ := hc
    rw [mk.injEq]
    ext x
    rw [Set.mem_preimage, Set.mem_preimage]
    rw [Set.mem_singleton_iff, Set.mem_singleton_iff]
    constructor
    {
      intro h
      have hc'' : g = (1/c) • f := by
        rw [hc', ←smul_assoc, smul_eq_mul]
        have h : (1/c) * c = 1 := by
          rw [one_div, mul_comm]
          exact IsUnit.mul_inv_cancel (isUnit_iff_ne_zero.mpr sorry /-hc-/)
        rw [h, one_smul]
      rw [hc'', AffineMap.coe_smul, Pi.smul_apply, h]
      exact smul_zero _
    }
    {
      intro h
      rw [hc', AffineMap.coe_smul, Pi.smul_apply, h]
      exact smul_zero c
    }
  }





/-- A relation that expresses that `H` and `H'` share a common boundary
  hyperplane. -/
abbrev Halfspace.is_opposite (H H' : Halfspace A) :=
  (H ∩ H' : Set A).is_hyperplane

def Halfspace.opposite' (H : Halfspace A) : Halfspace A
  := from_map (f := -H.map) (nconst_neg_nconst H.map_nonconst)

theorem Halfspace.opposite'.def (H : Halfspace A) :
    H.opposite'.is_opposite H := by
  unfold is_opposite
  unfold opposite'
  let ⟨ S, f, hf, hS ⟩ := H
  sorry

theorem Halfspace.opposite_symm {H H' : Halfspace A} (h : H.is_opposite H')
    : H'.is_opposite H := by
  unfold is_opposite
  rw [Set.inter_comm]
  exact h

lemma Halfspace.from_f_mf_opposite {f : A →ᵃ[𝕜] 𝕜} (h : ¬is_const f)
  : is_opposite (from_map (f :=  f) h)
                (from_map (f := -f) (nconst_neg_nconst h)) := sorry

theorem Halfspace.has_opposite (H : Halfspace A)
    : ∃ H', H.is_opposite H' := by
  let ⟨f, hc, hf⟩ := H.2
  have hc' : ¬is_const (-f) := by
    apply mt (const_neg_const (f := -f))
    rw [AffineMap.coe_neg, neg_neg]
    exact hc
  let H' := from_map (f := -f) hc'
  use H'
  unfold is_opposite Set.is_hyperplane
  use f
  constructor
  { exact hc }
  rw [hf]
  dsimp only
  have h : (-f) ⁻¹' Set.Ici 0 = f ⁻¹' Set.Iic 0 := by
    rw [AffineMap.coe_neg]
    unfold Set.Ici Set.Iic
    simp only [Set.preimage_setOf_eq, Pi.neg_apply, Left.nonneg_neg_iff]
  simp only [h]
  rw [←Set.preimage_inter, Set.Ici_inter_Iic_is_singleton]

theorem Halfspace.opposite_unique {H H1 H2 : Halfspace A}
  (h1 : H.is_opposite H1) (h2 : H.is_opposite H2)
    : H1 = H2 := by
  let ⟨ f, hf, hf' ⟩ := h1
  let ⟨ g, hg, hg' ⟩ := h2
  rw [Set.ext_iff] at hf' hg'
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff] at hf' hg'
  --have h := Π x : A, Iff.trans (hf' x).symm (hg' x)
  sorry

theorem Halfspace.has_unique_opposite (H : Halfspace A)
    : ∃! H', H.is_opposite H' :=
  exists_unique_of_exists_of_unique (has_opposite _) (@opposite_unique (H := H))

noncomputable def Halfspace.opposite (H : Halfspace A) : Halfspace A
  := Classical.choose (has_opposite H)

def Halfspace.boundary (H : Halfspace A) : Hyperplane A
  := Hyperplane.from_map (f := H.map) H.map_nonconst

theorem Halfspace.inter_of_opposite'_is_boundary (H : Halfspace A)
    : (H ∩ H.opposite' : Set A) = H.boundary := by
  unfold opposite' boundary
  rw [H.map_def]
  ext
  simp only [AffineMap.coe_neg, Set.mem_inter_iff, Set.mem_preimage, Set.mem_Ici,
    Pi.neg_apply, Left.nonneg_neg_iff, Set.mem_singleton_iff, le_antisymm_iff.symm]
  exact ⟨ symm, symm ⟩

theorem Hyperplane.has_halfspace_for_point (H : Hyperplane A)
  {x : A} (h : x ∉ (H : Set A))
    : ∃ H' : Halfspace A, x ∈ (H' : Set A) ∧ H = H'.boundary := by
  let f := H.map
  let H' := H.get_halfspace
  by_cases f x > 0
  case pos h =>
    use H'
    constructor
    rw [H'.map_def]
    unfold AffineMap.halfspace_carrier
    simp only [Set.mem_preimage, Set.mem_Ici]
    sorry
    sorry
  case neg h =>
    use H'.opposite
    constructor
    sorry
    sorry

-- instance Hyperplane.Nonempty (H : Hyperplane A)
--   : Nonempty H.1 := sorry

instance Hyperplane.AffineSubspace_non_empty (H : Hyperplane A)
  : Nonempty H.to_AffineSubspace := Set.nonempty_coe_sort.mpr H.nonempty

-- instance Hyperplane.to_AffineSpace (H : Hyperplane A)
--     : AffineSpace (H.to_AffineSubspace.direction) (H.to_AffineSubspace)
--   := H.to_AffineSubspace.to_AffineSpace

theorem Hyperplane.affine_space_codim_one [_root_.FiniteDimensional 𝕜 V] (H : Hyperplane A)
  : H.to_AffineSubspace.codim = 1 := by
  unfold AffineSubspace.codim
  sorry

theorem AffineSubspace.codim_one_is_hyperplane [VectorSpace.FiniteDimensional V]
  (E : AffineSubspace 𝕜 A) [Nonempty E] (h : E.codim = 1)
: E.carrier.is_hyperplane :=
  sorry

-- @[ext] -- Registers this as the extensionality lemma
-- lemma Halfspace.ext {H1 H2 : Halfspace A} (h : H1.1 = H2.1) : H1 = H2 := by
--   cases H1
--   cases H2
--   simp
--   exact h

-- example (H1 H2 : Halfspace A) : H1.1 = H2.1 → H1 = H2 := by
--   intro h; cases H1; cases H2; simp; exact h


def Hyperplane.subspace (H : Hyperplane A) : AffineSubspace 𝕜 A :=
  affineSpan 𝕜 H.1
