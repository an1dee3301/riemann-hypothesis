module

public import Mathlib
public import Init.Prelude
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Defs

@[expose] public section

namespace GlobalTheory.SumFourSwap

theorem sum_four_swap {R α β : Type} [AddCommMonoid R] [Fintype α] [Fintype β]
    (f : α → β → α → β → R) :
    ∑ a : α, ∑ b : β, ∑ c : α, ∑ e : β, f a b c e
      = ∑ c : α, ∑ e : β, ∑ a : α, ∑ b : β, f a b c e := by
  calc ∑ a : α, ∑ b : β, ∑ c : α, ∑ e : β, f a b c e
      = ∑ a : α, ∑ c : α, ∑ b : β, ∑ e : β, f a b c e :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ a : α, ∑ c : α, ∑ e : β, ∑ b : β, f a b c e :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => Finset.sum_comm
    _ = ∑ c : α, ∑ a : α, ∑ e : β, ∑ b : β, f a b c e := Finset.sum_comm
    _ = ∑ c : α, ∑ e : β, ∑ a : α, ∑ b : β, f a b c e :=
        Finset.sum_congr rfl fun c _ => Finset.sum_comm

end GlobalTheory.SumFourSwap
