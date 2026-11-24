module

public import Development.Core20Slim.Formalism.PeriodIntegrals.FglPhSplit
public import Init.Data.Cast
public import Init.Prelude
public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Data.Finset.Range
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.RingTheory.MvPowerSeries.Basic

@[expose] public section

noncomputable section

namespace PI.FglPhSplit.Wk

open PI.FglPhSplit MvPowerSeries


theorem coeff_expMv {K : Type} [Field K] {σ : Type} (f : MvPowerSeries σ K) (α : σ →₀ ℕ) :
    coeff α (expMv f) =
      ∑ n ∈ Finset.range ((α.sum fun _ k => k) + 1), coeff α (f ^ n) / (n.factorial : K) := rfl

end PI.FglPhSplit.Wk

end
