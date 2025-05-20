
import PolytopesInLEAN.Aux_General

variable {𝕜 : Type*} [LinearOrderedField 𝕜]

variable {V V' : Type*} [VectorSpace 𝕜 V] [VectorSpace 𝕜 V']
variable {A A' : Type*} [AffineSpace V A] [AffineSpace V' A']

/- Rays -/

open Function

def Set.is_ray (S : Set A) :=
  ∃ f : 𝕜 →ᵃ[𝕜] A, ¬is_const f ∧ S = f '' Set.Ici 0
  --:= ∃ p : A, ∃ v : V, S = { x : A | ∃ t ∈ 𝕜, t ≥ 0 ∧ x = t • v +ᵥ p}

abbrev Ray (A : Type*) [AffineSpace V A] := { S : Set A // S.is_ray }

-- structure Ray (A : Type*) [AffineSpace V A] where
--   set : Set A
--   is : set.is_ray
-- instance : Coe (Ray A) (Set A) := ⟨Ray.set⟩


namespace Ray -- param

  -- theorem has_param_rep(R : Ray A)
  --   : ∃ (p : A) (v : V), (R : Set A) = { q | ∃ t ∈ Set.Ici 0, q = t • v +ᵥ p } :=
  --   sorry

  def from_param' (p : A) (v : V) : Set A
    := (· • v +ᵥ p) '' Set.Ici 0
    -- := { q | ∃ t ∈ Set.Ici 0, q = t • v +ᵥ p }

  theorem from_param_is_ray (p : A) (v : V) : Set.is_ray (from_param' p v)
    := by sorry

  def from_param (p : A) (v : V) : Ray A
    := ⟨ _, from_param_is_ray p v ⟩

end Ray



theorem Ray.nonempty (R : Ray A) : Set.Nonempty R.1 := by
  let ⟨ S, f, h_fnc, h_f ⟩ := R
  dsimp only
  rw [h_f, Set.image_nonempty]
  exact Set.nonempty_Ici



def Set.is_line (S : Set A) :=
  ∃ f : 𝕜 →ᵃ[𝕜] A, ¬is_const f ∧ S = Set.range f

structure Line (A : Type*) [AffineSpace V A] where
  set : Set A
  is : set.is_line
instance : Coe (Line A) (Set A) := ⟨Line.set⟩




theorem Ray.not_point (R : Ray A) (x : A) : (R : Set A) ≠ {x} := by
  let ⟨ S, f, h_fnc, h_f ⟩ := R
  dsimp only
  by_contra h
  rw [h] at h_f
  unfold Set.image at h_f
  sorry

theorem Ray.affine_image_is_ray (R : Ray A) {f : A →ᵃ[𝕜] A'} (h_nc : ¬is_const f)
    : Set.is_ray (f '' R.1) := by
  obtain ⟨ _, g, h_nc', hg ⟩ := R
  unfold Set.is_ray
  use f.comp g
  constructor -- ∧
  { sorry }
  { sorry }

def Ray.affine_image (R : Ray A) {f : A →ᵃ[𝕜] A'} (h_nc : ¬is_const f) : Ray A' :=
  ⟨ _, Ray.affine_image_is_ray R h_nc ⟩

theorem Ray.restrict_is_ray (R : Ray A) {E : AffineSubspace 𝕜 A} [Nonempty E] (h : R.1 ⊆ E)
    : Set.is_ray (R ∩ᵣ E) := by
  sorry
  -- let ⟨S, f, h_nc, h_f⟩ := R
  -- simp
  -- simp at h
  -- unfold Set.is_ray
  -- let f' : 𝕜 →ᵃ[𝕜] E := f.restrict

def Ray.restr {R : Ray A} {E : AffineSubspace 𝕜 A} [Nonempty E] (h : R.1 ⊆ E) : Ray E
  := ⟨ R.1 ∩ᵣ E, R.restrict_is_ray h ⟩

theorem Ray.embed_is_ray {E : AffineSubspace 𝕜 A} [Nonempty E] (R : Ray E)
    : Set.is_ray (R.1 ↑ₑ A) := by
  let ⟨S, f, h_nc, h_f⟩ := R
  exact ⟨ f.extend_codom, AffineMap.extend_non_const h_nc, AffineMap.image_extend_codom h_f ⟩

def Ray.embed {E : AffineSubspace 𝕜 A} [Nonempty E] (R : Ray E) : Ray A
  := ⟨ R.1 ↑ₑ A, R.embed_is_ray ⟩

def Set.ray_bounded (S : Set A) := ∀ R : Ray A, ¬(R.1 ⊆ S)

theorem empty_is_ray_bounded (A : Type*) [AffineSpace V A] : Set.ray_bounded (∅ : Set A) := by
  unfold Set.ray_bounded
  intro R
  rw [Set.subset_empty_iff]
  exact Set.nonempty_iff_ne_empty.mp R.nonempty

theorem point_is_ray_bounded (x : A) : Set.ray_bounded {x} := by
  unfold Set.ray_bounded
  intro R
  --by_contra h
  rw [Set.subset_singleton_iff_eq]
  push_neg
  constructor
  { exact R.nonempty }
  { exact R.not_point x }

theorem Set.Ici.ray_unbounded (x : 𝕜) : ¬ray_bounded (Set.Ici x) := by
  -- unfold Set.ray_bounded
  -- push_neg
  -- use ⟨ Set.Ici x, AffineMap.id 𝕜 𝕜, _, _ ⟩
  sorry

theorem AffineMap.preimage_ray_unbounded (f : A →ᵃ[𝕜] A') {S : Set A'} (h : ¬S.ray_bounded)
    : ¬(f ⁻¹' S).ray_bounded := by
  by_cases h_const : is_const f
  {
    by_cases h_dim : AffineSpace.dim A = 0
    { sorry }
    { sorry }
  }
  unfold Set.ray_bounded
  unfold Set.ray_bounded at h
  push_neg
  push_neg at h
  obtain ⟨ R, hR ⟩ := h
  -- use R.affine_image h
  sorry

theorem AffineMap.image_ray_bounded (f : A →ᵃ[𝕜] A') {S : Set A} (h : S.ray_bounded)
    : (f '' S).ray_bounded := by
  unfold Set.ray_bounded
  unfold Set.ray_bounded at h
  intro R
  -- let h := h R
  sorry

theorem Set.subset_of_ray_bounded (S T : Set A) (h : S ⊆ T)
    : T.ray_bounded → S.ray_bounded := by
  rw [←not_imp_not]
  intro h_nbd
  unfold Set.ray_bounded at h_nbd
  push_neg at h_nbd
  let ⟨ r, h_r ⟩ := h_nbd
  unfold Set.ray_bounded
  push_neg
  use r
  exact subset_trans h_r h

theorem Set.restrict_of_ray_bounded (S : Set A) (E : AffineSubspace 𝕜 A) [Nonempty E]
    : S.ray_bounded → (S ∩ᵣ E).ray_bounded := by
  rw [←not_imp_not]
  intro h_nbd
  unfold Set.ray_bounded at h_nbd
  push_neg at h_nbd
  let ⟨ r, h_r ⟩ := h_nbd
  unfold Set.ray_bounded
  push_neg
  use r.embed
  have h := AffineSubspace.embed_subset_rel h_r
  rewrite [AffineSubspace.embed_of_restrict] at h
  exact subset_trans h Set.inter_subset_left

theorem Set.embed_of_ray_bounded {E : AffineSubspace 𝕜 A} [Nonempty E] (S : Set E)
    : S.ray_bounded → (S ↑ₑ A).ray_bounded := by
  rw [←not_imp_not]
  intro h_nbd
  unfold Set.ray_bounded at h_nbd
  push_neg at h_nbd
  let ⟨ R, h_R ⟩ := h_nbd
  unfold Set.ray_bounded
  push_neg
  have h1 : (S ↑ₑ A) ⊆ E := by
    unfold AffineSubspace.embed
    rw [Set.subset_def]
    intro x hx
    simp at hx
    let ⟨ h_xin, _ ⟩ := hx
    exact h_xin
  use R.restr (subset_trans h_R h1)
  apply AffineSubspace.restr_subset_rel at h_R
  rw [AffineSubspace.restrict_of_embed] at h_R
  apply h_R
  exact inferInstance

def Set.ray_boundary (S : Set A) : Set A
  := { x : A | ∃ R : Ray A, R.1 ∩ S = { x } }
