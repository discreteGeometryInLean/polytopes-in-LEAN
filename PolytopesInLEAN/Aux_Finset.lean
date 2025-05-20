
import Mathlib.Data.Set.Card
import Mathlib.Data.Finset.Basic

noncomputable section

namespace Finset

  -- def biInter {α ι : Type*} [Nonempty ι] (f : ι → Finset α) : Finset α :=
  --   @Set.Finite.toFinset _ (⋂ x, f x) (by
  --     let x : ι := Classical.choice inferInstance
  --     apply Set.Finite.subset (Finset.finite_toSet (f x))
  --     apply Set.iInter_subset
  --   )

  -- def biInter' {α : Type*} (S : Set (Finset α)) [Nonempty S] : Finset α :=
  --   @Set.Finite.toFinset _ (⋂₀ (Finset.toSet '' S)) (by
  --     let x : S := Classical.choice inferInstance
  --     apply Set.Finite.subset (Finset.finite_toSet x)
  --     simp
  --     apply Set.iInter_subset
  --     sorry
  --   )

  /-- Notation used if the result should be a Finset. This is necessarily the union/intersection
    of a Finset of Finsets. -/

  --notation "⋂₀ᶠ" S => Finset.biInter S id
  notation "⋃₀ᶠ" S => Finset.biUnion S id

  notation f "''ᶠ" S => Finset.image f S

end Finset
