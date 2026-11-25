module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchwartzGaussianFormReNeg
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairInfApply
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockFormApply
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic

@[expose] public section

open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gaussian_form_re_neg_of_ne_zero : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (M : V →ₗ[ℝ] V →ₗ[ℝ] ℂ) (g : SchwartzMap V ℂ), g ≠ 0 →
    (∀ x, g x = g 0 * Complex.exp (M x x)) → ∀ v, v ≠ 0 → (M v v).re < 0 := by
  first | exact @GlobalTheory.schwartz_gaussian_form_re_neg | exact GlobalTheory.schwartz_gaussian_form_re_neg | (intros; apply GlobalTheory.schwartz_gaussian_form_re_neg <;> assumption)
