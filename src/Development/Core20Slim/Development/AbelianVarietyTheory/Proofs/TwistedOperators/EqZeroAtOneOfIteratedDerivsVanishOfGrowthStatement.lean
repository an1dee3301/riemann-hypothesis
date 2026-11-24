module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqZeroAtOneOfIteratedDerivsVanishOfGrowth
public import Init.Data.Cast
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Topology.MetricSpace.Algebra
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_zero_at_one_of_iteratedDerivs_vanish_of_growth : ∀ (φ : ℕ → ℝ → ℂ) (a b : ℝ), (∀ k t, HasDerivAt (φ k) (φ (k + 1) t) t) → (∀ k, φ k 0 = 0) → (∀ k t, ‖φ k t‖ ^ 2 ≤ b * a ^ k * k.factorial) → φ 0 1 = 0 := by
  first | exact @GlobalTheory.vanish_at_one_of_derivs_vanish_of_growth | exact GlobalTheory.vanish_at_one_of_derivs_vanish_of_growth | (intros; apply GlobalTheory.vanish_at_one_of_derivs_vanish_of_growth <;> assumption)
