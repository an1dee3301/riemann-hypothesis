module

public import Mathlib
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.NeZero
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.Group.Defs
public import Mathlib.Algebra.Order.ZeroLEOne
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Finite.Lemmas
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Lattice
public import Mathlib.Tactic.CancelDenoms.Core
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

namespace Bl.FirstLemmaK

theorem goal1 :
  ∀ {α : Type} {S : Set.{0} α},
  Set.Finite.{0} S →
    ∀ (f : α → Real),
      (∀ (x : α), Membership.mem.{0, 0} S x → LT.lt.{0} 0 (f x)) →
        Exists.{1} fun (r : Real) ↦
          And (LT.lt.{0} 0 r) (And (LE.le.{0} r 1) (∀ (x : α), Membership.mem.{0, 0} S x → LT.lt.{0} r (f x))) := by
  intro α S hS f hf
  rcases S.eq_empty_or_nonempty with h | hne
  · refine ⟨1, one_pos, le_rfl, ?_⟩
    intro x hx
    rw [h] at hx
    exact absurd hx (Set.notMem_empty x)
  · obtain ⟨a, ha, hmin⟩ := Set.exists_min_image S f hS hne
    have hfa : 0 < f a := hf a ha
    refine ⟨min (f a) 1 / 2, ?_, ?_, ?_⟩
    · have : 0 < min (f a) 1 := lt_min hfa one_pos
      linarith
    · have : min (f a) 1 ≤ 1 := min_le_right _ _
      linarith
    · intro x hx
      have h1 : min (f a) 1 ≤ f a := min_le_left _ _
      have h2 : f a ≤ f x := hmin x hx
      have : 0 < min (f a) 1 := lt_min hfa one_pos
      linarith

end Bl.FirstLemmaK
