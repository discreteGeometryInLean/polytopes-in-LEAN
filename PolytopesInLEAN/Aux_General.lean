
import Mathlib.Data.Subtype
import Mathlib.Data.Finite.Card
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card

import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.SetTheory.Cardinal.Finite

import Mathlib.LinearAlgebra.Dimension.Basic
import Mathlib.LinearAlgebra.FiniteDimensional

import Mathlib.LinearAlgebra.AffineSpace.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace
import Mathlib.LinearAlgebra.AffineSpace.AffineMap
import Mathlib.LinearAlgebra.AffineSpace.Restrict
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

import Mathlib.Algebra.Module.Submodule.Defs
import Mathlib.Algebra.Module.Submodule.LinearMap

import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Convex.Hull

noncomputable section

variable {α β γ : Type*}

/- VectorSpace -/

/-- `VectorSpace` bundles a module with the semiring and has the advantage that
  the semiring needs not be stated explicitly at every use. -/
class VectorSpace (𝕜 : outParam Type*) [Semiring 𝕜] (V : Type*)
  extends AddCommGroup V, Module 𝕜 V --, FiniteDimensional 𝕜 V

/- NOTE: As far as I can tell, it is not possible with mathlib structure to
  implement at the same time tropical vector spaces. The main reason seems to be
  that `Module` is always a commutative additive group. -/

/- We will mostly assume a linearly ordered field, but this can likely be relaxed. -/
variable {𝕜 : Type*} [Field 𝕜]

instance : VectorSpace 𝕜 𝕜 := VectorSpace.mk

variable {V: Type*} [VectorSpace 𝕜 V]

namespace VectorSpace

  variable (V)

  abbrev cdim : Cardinal := Module.rank 𝕜 V
  abbrev dim : ℕ := Module.finrank 𝕜 V

  -- NOTE: This is a typeclass due to transparent abbrev.
  abbrev FiniteDimensional := _root_.FiniteDimensional 𝕜 V
  abbrev InfiniteDimensional := ¬FiniteDimensional V

end VectorSpace

namespace Submodule

  variable (E : Submodule 𝕜 V)

  instance to_VectorSpace : VectorSpace 𝕜 E :=
    @VectorSpace.mk _ _ _ E.addCommGroup E.module

  attribute [local instance] Classical.propDecidable

  abbrev cdim : Cardinal := Module.rank 𝕜 E
  abbrev dim : ℕ := Module.finrank 𝕜 E
  def sdim : ℤ := if _ : Nonempty E then E.dim else -1

  def codim [VectorSpace.FiniteDimensional V] : Nat
    := (VectorSpace.dim V) - E.dim

  abbrev FiniteDimensional := VectorSpace.FiniteDimensional E
  abbrev InfiniteDimensional := ¬FiniteDimensional E

end Submodule


/- AffineSpace -/

/-- A version of affine space that uses `VectorSpace`. The advantage over mathlib's
  native `AffineSpace` is that the underlying field is part of the structure and
  needs not be stated explicitly. -/
class AffineSpace {𝕜 : outParam Type*} [Semiring 𝕜]
    (V : outParam Type*) [VectorSpace 𝕜 V]
    (A : Type*)
  extends AddTorsor V A

variable {A : Type*} [AffineSpace V A]

instance VectorSpace.to_AffineSpace : AffineSpace V V
  := AffineSpace.mk

namespace AffineSpace

  abbrev cdim (A : Type*) [AffineSpace V A]
    : Cardinal := VectorSpace.cdim V
  abbrev dim (A : Type*) [AffineSpace V A] -- [FiniteDimensional 𝕜 V]
    : ℕ := VectorSpace.dim V

  -- NOTE: This is a typeclass due to transparent abbrev.
  abbrev FiniteDimensional (A : Type*) [AffineSpace V A]
    := VectorSpace.FiniteDimensional V
  abbrev InfiniteDimensional (A : Type*) [AffineSpace V A]
    := ¬FiniteDimensional A

  theorem cdim_zero_is_subsingleton (h : cdim A = 0) : Subsingleton A := by
    unfold cdim at h
    rw [rank_zero_iff] at h
    rw [AddTorsor.subsingleton_iff V A] at h
    exact h

  theorem dim_zero_is_subsingleton [FiniteDimensional V] (h : dim A = 0) : Subsingleton A := by
    unfold dim at h
    rw [finrank_zero_iff_forall_zero] at h
    have s : Subsingleton V
      := Subsingleton.intro (by simp [h])
    exact (AddTorsor.subsingleton_iff V A).mp s

end AffineSpace

namespace AffineSubspace

  variable (E : AffineSubspace 𝕜 A)

  /- NOTE: mathlib contains tools to convert an `AffineSubspace` into an `AddTorsor`
  via the function `AffinSubspace.toAddTorsor`. But they make it an abbrev as
  opposed to an instance (hence not available to automatic typeclass inference)
  because this led to some loops with NonEmpty. Hence, to infer AddTorsor from
  an `E : AffineSubspace` we need to invoke `E.toAddTorsor` explicitly.
  -/
  instance to_AffineSpace [Nonempty E]
      : AffineSpace (E.direction) E :=
    @AffineSpace.mk _ _ _ _ _ E.toAddTorsor

  /- `AffineSubpace` coerces to `AffineSpace`, for which a `FiniteDimensional` is already
    implemented. However, an `AffineSubspace` can be empty, while an `AffineSpace` cannot.
    These definitions therefore work even if `Nonempty` in not available. -/
  abbrev cdim : Cardinal := E.direction.cdim
  abbrev dim : ℕ := E.direction.dim
  def sdim : ℤ := E.direction.sdim

  def codim [AffineSpace.FiniteDimensional A] : Nat := E.direction.codim

  abbrev FiniteDimensional := E.direction.FiniteDimensional
  abbrev InfiniteDimensional := ¬FiniteDimensional E

  /- TODO: make `AffineSubspace.restr` and `.embed` classes, and make an instance for
    `AffinSubspace`, so they can be used for other types than affine spaces. -/
  -- def restrict {α : Type*} (A B : Set α) : Set B := { x : B | (x : α) ∈ A }

  /-- Intersects a subset of an `AffineSpace` with an `AffineSubspace`, and considers
    the result as a subset of the `AffineSubspace`. -/
  abbrev restr (S : Set A) (E : AffineSubspace 𝕜 A) : Set E
    := { x : E | (x : A) ∈ S }

  /-- Considers a subset of an `AffineSubspace E` of an `AffineSpace A` as a
    subset of the `AffineSpace A` itself. -/
  abbrev embed (A : Type*) [AffineSpace V A]
    {E : AffineSubspace 𝕜 A} (S : Set E) : Set A
    := {x : A | ∃ y ∈ S, (y : A) = x}

  infixl:80 " ∩ᵣ " => AffineSubspace.restr
  notation:80 S " ↑ₑ " A => AffineSubspace.embed A S

  theorem restrict_of_embed {E : AffineSubspace 𝕜 A} [Nonempty E] (S : Set E)
      : ((S ↑ₑ A) ∩ᵣ E) = S := by
    unfold restr embed
    simp only [Subtype.exists, exists_and_right, exists_eq_right, Set.mem_setOf_eq,
      Subtype.coe_eta, SetLike.coe_mem, exists_const, Set.setOf_mem_eq]

  theorem embed_of_restrict (S : Set A) (E : AffineSubspace 𝕜 A) [Nonempty E]
      : ((S ∩ᵣ E) ↑ₑ A) = S ∩ E := by
    unfold restr embed
    rw [Set.inter_def]
    simp only [Set.mem_setOf_eq, Subtype.exists, exists_and_left, exists_prop,
      exists_eq_right_right, SetLike.mem_coe]

  theorem restr_subset_rel {S T : Set A} {E : AffineSubspace 𝕜 A} [Nonempty E]
      (h : S ⊆ T) : (S ∩ᵣ E) ⊆ (T ∩ᵣ E) := by
    unfold restr
    simp only [Set.setOf_subset_setOf, Subtype.forall]
    intro _ _ h_in
    exact Set.mem_of_mem_of_subset h_in h

  theorem embed_subset_rel {E : AffineSubspace 𝕜 A} [Nonempty E]
      {S T : Set E} (h : S ⊆ T) : (S ↑ₑ A) ⊆ (T ↑ₑ A) := by
    unfold embed
    simp only [Subtype.exists, exists_and_right, exists_eq_right,
      Set.setOf_subset_setOf, forall_exists_index]
    intro _ h_a h_in
    use h_a
    exact Set.mem_of_mem_of_subset h_in h

end AffineSubspace





abbrev Set.FiniteDimensional (S : Set A) := (affineSpan 𝕜 S).FiniteDimensional

namespace Set

  variable {α : Type*} (S : Set α)

  /-- `S : Set α` is nonempty as a set if and only if it is nonempty as a type. -/
  theorem Nonempty_nonempty_iff
      : Nonempty S ↔ S.Nonempty := by
    rw [nonempty_subtype]; rfl

  instance {α : Type*} {S : Set α} {h : S.Nonempty} : Nonempty S
    := (Nonempty_nonempty_iff S).mpr h

end Set



namespace Basis

  variable {S : Set V} (hs : LinearIndependent 𝕜 ((↑) : S → V))

  /-- Index set used by the basis extension constructed via `Basis.extend`. -/
  abbrev extend_index := hs.extend (Set.subset_univ S)

  /-- If `B` is a basis that extends a set `S`, then `S` embeds into the index set
    of this basis in a natural way. -/
  def extend_index_embed : S ↪ (extend_index hs) where
    toFun := fun x => ⟨ x, by
      apply subset_extend
      simp only [Subtype.coe_prop] ⟩
    inj' := by
      unfold Function.Injective
      simp only [Subtype.mk.injEq, Subtype.forall, imp_self, implies_true]

  /-- The embedding of the set `S` into the index set of its basis extension
    is such that each `x` in `S` is sent to an index that, when sent through
    the basis, gives the vector `x`. -/
  def extend_index_embed_self (x : S)
      : extend hs (extend_index_embed hs x) = x := by
    rw [coe_extend]; rfl

  abbrev extend_index_of {x : V} (h_mem : x ∈ S)
      : extend_index hs := ⟨ x, by apply hs.subset_extend; exact h_mem ⟩

  def extend_index_of_def {x : V} (h_mem : x ∈ S)
      : extend hs (extend_index_of (x := x) _ h_mem) = x := by
    rw [coe_extend]

  -- @[simp]
  -- theorem constr_basis' {ι : Type*} {b : Basis ι 𝕜 V} (f : ι → V') {x : V} (mem : x ∈ Set.range b)
  --     : (constr (M' := V') b 𝕜 f : V → V') (b i) = f i := by
  --   simp [Basis.constr_apply, b.repr_self]

  /-- `Basis.extend` contains the generators. -/
  theorem extend_subset_range : S ⊆ Set.range (extend hs) := by
    rw [range_extend]
    exact subset_extend hs

  /-- If the set `S` is nonempty, then the index set of a basis extension
    is Nonempty. -/
  instance extend_index_Nonempty (h_ne : S.Nonempty)
      : Nonempty (extend_index hs) :=
    Set.range_nonempty_iff_nonempty.mp (h_ne.mono (extend_subset_range hs))

end Basis




namespace Function

  -- MathLib defines constant functions but seems to not define a predicate that tests for const
  -- Our definitions of this test do not need α to be inhabited.

  -- class Const {α β : Type*} (f : α → β) : Prop where
  --   const : ∃ q : β, ∀ x : α, f x = q

  -- class NonConst {α β : Type*} (f : α → β) : Prop where
  --   nconst : ∀ x y, f x = f y

  abbrev is_const (f : α → β)
    := ∀ x y, f x = f y

  abbrev is_nonconst (f : α → β)
    := ¬is_const f
  -- alias nonconst := is_nonconst

  abbrev is_const' (f : α → β)
    := ∃ q, f = const α q

  lemma is_const_impl {f : α → β} (h : f.is_const')
      : f.is_const := by
    intro x y
    let ⟨_, hq⟩ := h
    simp only [hq, const_apply]

  lemma is_const_impl' {f : α → β} [Nonempty α] (h : f.is_const)
      : f.is_const' := by
    use f (Classical.arbitrary α)
    apply funext
    intro x
    simp only [const_apply]
    apply h

  lemma is_const_equiv (f : α → β) [Nonempty α]
      : f.is_const ↔ f.is_const' := ⟨ f.is_const_impl', f.is_const_impl ⟩

  /-- Composing a function with a constant function from the right yields a
    constant function -/
  def comp_right_const_is_const (f : β → γ) {g : α → β} (hg : g.is_const)
  : (f ∘ g).is_const := by
    intro x y
    simp only [comp_apply]
    rw [hg x y]

  /-- Composing a function with a constant function from the left yields a
    constant function -/
  def comp_left_const_is_const {f : β → γ} (hf : f.is_const) (g : α → β)
  : (f ∘ g).is_const := by
    intro x y
    simp only [comp_apply]
    rw [hf (g x) (g y)]

  /-- If a function `f` is a constant, then so is `-f`. -/
  lemma const_neg_const {α : Type*} {f : α → 𝕜} (h : is_const f)
      : is_const (-f) := comp_right_const_is_const (-·) h
  -- NOTE: can we utilize Function.const_neg ?

  /-- If a function `f` is a constant, then so is `-f`. -/
  lemma nconst_neg_nconst {α : Type*} {f : α → 𝕜} (h : ¬is_const f)
      : ¬is_const (-f) := by
    apply mt const_neg_const
    rw [neg_neg]
    exact h


end Function





variable {V' : Type*} [VectorSpace 𝕜 V']

namespace LinearMap

  open Basis

  variable (V V' : Type*) [VectorSpace 𝕜 V] [VectorSpace 𝕜 V']

  theorem exists_non_const [Nontrivial V] [Nontrivial V']
      : ∃ f : V →ₗ[𝕜] V', ¬f.toFun.is_const := by
    have ⟨ x, hx ⟩ := exists_ne (0 : V)
    have ⟨ y, hy ⟩ := exists_ne (0 : V')
    have h_li := linearIndependent_singleton (R := 𝕜) hx
    let b := extend (s := {x}) h_li
    use constr b 𝕜 (fun _ => y) -- constructs a linear map that sends all basis elements to y
    unfold Function.is_const
    push_neg
    --
    have := extend_index_Nonempty h_li (Set.singleton_nonempty x)
    let i := Classical.arbitrary (extend_index h_li)
    use 0, b i
    simp only [AddHom.toFun_eq_coe, coe_toAddHom, map_zero]
    rw [constr_basis b 𝕜 (fun _ => y) _]
    exact hy.symm

  theorem zero_is_const : Function.is_const (0 : V →ₗ[𝕜] V') := fun _ _ => rfl

  instance [Nontrivial V] [Nontrivial V'] : Nontrivial (V →ₗ[𝕜] V') where
    exists_pair_ne := by
      let ⟨ f, hf ⟩ := exists_non_const V V'
      use 0, f
      by_contra h
      rw [←h] at hf
      exact hf (zero_is_const V V')

end LinearMap

namespace AddTorsor

  variable {G : Type*} [AddGroup G] (A : Type*) [AddTorsor G A]

  theorem nontrivial_impl_nontrivial_group [Nontrivial A] : Nontrivial G where
    exists_pair_ne := by
      have x := Classical.arbitrary A
      let ⟨ y, hy ⟩ := exists_ne x
      use 0, (x -ᵥ y)
      simp only [ne_eq, ←vsub_ne_zero, vsub_eq_sub, zero_sub, neg_vsub_eq_vsub_rev,
        vsub_eq_zero_iff_eq, hy, not_false_eq_true]

  theorem nontrivial_from_nontrivial_group [Nontrivial G] : Nontrivial A where
    exists_pair_ne := by
      have p := Classical.arbitrary A
      let ⟨ v, hv ⟩ := exists_ne (0 : G)
      use p, (v +ᵥ p)
      rw [ne_eq, ←vsub_left_cancel_iff (p := p), vsub_self, vadd_vsub]
      exact hv.symm

  theorem nontrivial_impl_nontrivial_group_iff : Nontrivial G ↔ Nontrivial A := ⟨
      fun _ => nontrivial_from_nontrivial_group A,
      fun _ => nontrivial_impl_nontrivial_group A
    ⟩

end AddTorsor

variable {V' : Type*} [VectorSpace 𝕜 V']
variable {A' : Type*} [AffineSpace V' A']

namespace AffineBasis

  variable {ι : Type*}

  def constr'' (p₀ : A) (p₀' : A') (b : Basis ι 𝕜 V) (p : ι → V')
      : A →ᵃ[𝕜] A' where
    toFun := fun x => (Basis.constr b 𝕜 p (x -ᵥ p₀)) +ᵥ p₀'
    linear := Basis.constr b 𝕜 p
    map_vadd' := by
      intro p1 v
      rw [←vadd_assoc, vadd_eq_add, vadd_right_cancel_iff, ←LinearMap.map_add,
        vadd_vsub_assoc]

  def constr' (i : ι) (b : AffineBasis ι 𝕜 A) (p : ι → A') : A →ᵃ[𝕜] A'
    := constr'' (b i) (p i) (AffineBasis.basisOf b i) (fun x => (p x -ᵥ p i))

  /-- An affine map that sends each element of an affine basis onto a prescribed
    point. -/
  def constr (b : AffineBasis ι 𝕜 A) (p : ι → A') : A →ᵃ[𝕜] A'
    := constr' (Classical.choice b.nonempty) b p

  theorem constr''_basis (p₀ : A) (p₀' : A') (b : Basis ι 𝕜 V) (p : ι → V') (i : ι)
      : constr'' p₀ p₀' b p (b i +ᵥ p₀) = p i +ᵥ p₀' := by
    unfold constr''
    simp only [AffineMap.map_vadd, Basis.constr_basis, AffineMap.coe_mk, vsub_self,
      map_zero, zero_vadd]

  theorem constr''_basis' (p₀ : A) (p₀' : A') (b : Basis ι 𝕜 V) (p : ι → V')
      : constr'' p₀ p₀' b p p₀ = p₀' := by
    unfold constr''
    rw [AffineMap.coe_mk, vsub_self, map_zero, zero_vadd]

  theorem constr'_basis (i : ι) (b : AffineBasis ι 𝕜 A) (p : ι → A') (j : ι)
      : constr' i b p (b j) = p j := by
    unfold constr'
    by_cases j = i
    case pos h =>
      rw [h]
      exact constr''_basis' (b i) (p i) (AffineBasis.basisOf b i) (fun x => (p x -ᵥ p i))
    case neg h =>
      have h := constr''_basis (b i) (p i) (AffineBasis.basisOf b i) (fun x => (p x -ᵥ p i)) ⟨j, h⟩
      rw [basisOf_apply] at h
      simp only [ne_eq, vsub_vadd] at h
      exact h

  theorem constr_basis (b : AffineBasis ι 𝕜 A) (p : ι → A') (i : ι)
      : constr b p (b i) = p i := constr'_basis _ b p i

end AffineBasis

namespace AffineMap

  open Function
  open AddTorsor

  theorem is_const_iff_linear_is_const (f : A →ᵃ[𝕜] A')
      : is_const f ↔ is_const f.linear := by
    unfold is_const
    constructor
    all_goals intro h x y
    {
      let p := Classical.arbitrary A
      have h := h (x +ᵥ p) (y +ᵥ p)
      simp only [map_vadd, vadd_right_cancel_iff] at h
      exact h
    }
    {
      have h := h 0 (x -ᵥ y)
      simp only [map_zero, linearMap_vsub] at h
      rw [←vsub_eq_zero_iff_eq]
      exact h.symm
    }

  theorem exists_non_const (A A' : Type*) [AffineSpace V A] [AffineSpace V' A']
    [Nontrivial A] [Nontrivial A']
      : ∃ f : A →ᵃ[𝕜] A', ¬is_const f := by
    have := nontrivial_impl_nontrivial_group A
    have := nontrivial_impl_nontrivial_group A'
    let x  := Classical.arbitrary A
    let x' := Classical.arbitrary A'
    let ⟨ f', hf' ⟩ := LinearMap.exists_non_const V V'
    use ⟨ fun p => f' (p -ᵥ x) +ᵥ x', f', by
      intro a v
      simp only [←vadd_assoc, vadd_right_cancel_iff, vadd_vsub_assoc, map_add, vadd_eq_add]
    ⟩
    rw [is_const_iff_linear_is_const]
    exact hf'

end AffineMap



-- def AffineMap.constant (f : A →ᵃ[𝕜] 𝕜)
--   : Prop := ∃q : 𝕜, f = Function.const A q

namespace AffineMap

  open Function

  lemma non_const_form_is_surj {f : A →ᵃ[𝕜] 𝕜} (h : ¬is_const f)
      : Surjective f := by
    intro b
    unfold is_const at h
    push_neg at h
    let ⟨ x, y, h ⟩ := h
    use ((b - f x) / (f x - f y)) • (x -ᵥ y) +ᵥ x
    rw [map_vadd, map_smul, linearMap_vsub, vsub_eq_sub, smul_eq_mul, vadd_eq_add,
      mul_comm, mul_div_cancel₀, sub_add_cancel]
    exact sub_ne_zero_of_ne h

end AffineMap

variable {V' : Type*} [VectorSpace 𝕜 V']

namespace LinearMap

  abbrev restrict_dom (f : V →ₗ[𝕜] V') (E : Submodule 𝕜 V) : E →ₗ[𝕜] V' where
    toFun := fun x : E ↦ f x
    map_add' := by simp only [Submodule.coe_add, map_add, implies_true]
    map_smul' := by simp only [SetLike.val_smul, map_smul, RingHom.id_apply, implies_true]

  abbrev extend_codom (E : Submodule 𝕜 V) (f : V' →ₗ[𝕜] E) : V' →ₗ[𝕜] V where
    toFun := fun x ↦ (f x : V)
    map_add' := by simp only [map_add, Submodule.coe_add, implies_true]
    map_smul' := by simp only [map_smul, SetLike.val_smul, RingHom.id_apply, implies_true]

end LinearMap

variable {A' : Type*} [AffineSpace V' A']

namespace AffineMap

  abbrev restrict_dom (f : A →ᵃ[𝕜] A') (E : AffineSubspace 𝕜 A) [Nonempty E]
      : E →ᵃ[𝕜] A' where
    toFun := fun x : E ↦ f x
    linear := f.linear.restrict_dom E.direction
    map_vadd' := by
      unfold LinearMap.restrict_dom
      simp only [AffineSubspace.coe_vadd, map_vadd, LinearMap.coe_mk, AddHom.coe_mk, implies_true]
    -- @AffineMap.restrict 𝕜 V A 𝕜 𝕜 _ _ _ _ _ _ _ f E ⊤ _ _ (f.restrImageInTopSubspace E)
    --f.restrict (f.restrImageInTopSubspace E)

  abbrev extend_codom {E : AffineSubspace 𝕜 A} [Nonempty E] (f : A' →ᵃ[𝕜] E)
      : A' →ᵃ[𝕜] A where
    toFun := fun x => (f x : A)
    linear := f.linear.extend_codom E.direction
    map_vadd' := by
      unfold LinearMap.extend_codom
      simp only [map_vadd, AffineSubspace.coe_vadd, LinearMap.coe_mk, AddHom.coe_mk, implies_true]

  -- theorem restrict_dom.id (f : A →ᵃ[𝕜] 𝕜) (E : AffineSubspace 𝕜 A) [Nonempty E]
  --   : ∀ x : E, f x = (f.restrict_dom E) x := by
  --   intro x
  --   unfold restrict_dom
  --   simp

  /-- If the preimage of an affine map is restricted to an affine subspace, then this
    restriction is again the preimage of an affine map. -/
  theorem preimage_restrict_dom {S : Set A} {T : Set A'} {f : A →ᵃ[𝕜] A'} (h : S = f ⁻¹' T)
    (E : AffineSubspace 𝕜 A) [Nonempty E]
      : (S ∩ᵣ E) = (f.restrict_dom E) ⁻¹' T := by
    unfold AffineSubspace.restr
    rw [h]
    unfold Set.preimage
    simp only [Set.mem_setOf_eq, coe_mk]

  /-- If the image of an affine map is emebdded into a larger affine space, then this
    embedding is again the image of an affine map. -/
  theorem image_extend_codom {E : AffineSubspace 𝕜 A'} [Nonempty E]
    {S : Set A} {T : Set E} {f : A →ᵃ[𝕜] E} (h : T = f '' S)
      : (T ↑ₑ A') = f.extend_codom '' S := by
    unfold AffineSubspace.embed
    rw [h]
    unfold Set.image
    simp only [Set.mem_setOf_eq, exists_exists_and_eq_and, coe_mk]

  /-- Extending a non-constant affine map yields a non-constant affine map. -/
  theorem extend_non_const {E : AffineSubspace 𝕜 A'} [Nonempty E]
    {f : A →ᵃ[𝕜] E} (h : ¬Function.is_const f)
      : ¬Function.is_const (f.extend_codom) := by
    unfold Function.is_const at h
    push_neg at h
    let ⟨ x, y, hxy ⟩ := h
    unfold Function.is_const
    push_neg
    use x; use y; simp
    exact hxy

end AffineMap




/-- The intersection of [-inf, a] and [a, inf] is {a} -/
lemma Set.Ici_inter_Iic_is_singleton {𝕜 : Type*} [LinearOrderedSemiring 𝕜] (a : 𝕜)
    : Ici a ∩ Iic a = {a} := by
  rw [Ici_inter_Iic]
  exact Icc_self a



/- Specialized inductions -/

namespace Set.Finite

  /-- Specialized induction on finite sets: proving that a proporitions C holds for all finite sets by proving
    it for the empty set, the singleton, and the union of two sets that satisfy C. -/
  @[elab_as_elim]
  theorem union_induction_on {C : Set α → Prop} {S : Set α} (h : S.Finite)
      (H0 : C ∅)
      (H1 : ∀ x, C {x})
      (Hun : ∀ {s t}, s.Finite → t.Finite → C s → C t → C (s ∪ t)) : C S := by
    induction S, h using dinduction_on
    case H0 =>
      exact H0
    case H1 a S hS hfin hC =>
      rw [←Set.singleton_union]
      exact Hun (finite_singleton a) hfin (H1 a) hC

  /-- Specialized dependent induction on finite sets: proving that a propositions C holds for all finite sets by proving
    it for the empty set, the singleton, and the union of two sets that satisfy C. -/
  @[elab_as_elim]
  theorem union_dinduction_on {C : ∀ s : Set α, s.Finite → Prop} (s : Set α) (h : s.Finite)
      (H0 : C ∅ finite_empty)
      (H1 : ∀ x, C {x} (finite_singleton x))
      (Hun : ∀ {s t}, ∀ hs : Set.Finite s, ∀ ht : Set.Finite t, C s hs → C t ht → C (s ∪ t) (union hs ht))
      : C s h := by
    have : ∀ h : s.Finite, C s h :=
      union_induction_on h
        (fun _ => H0)
        (fun x _ => H1 x)
        (fun sfin tfin hs ht _ => Hun sfin tfin (hs sfin) (ht tfin))
    exact this h

end Set.Finite
