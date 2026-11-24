module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchwartzEqZeroOfWrongSignGaussianRelation
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_eq_zero_of_wrong_sign_gaussian_relation : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (f : SchwartzMap V ℂ) (a₁ a₂ : V) (ℓ₁ ℓ₂ : V →ₗ[ℝ] ℝ),
    (∀ y, fderiv ℝ f y a₂ + (-(2 * Real.pi * Complex.I) * (ℓ₂ y : ℂ)) * f y =
      Complex.I * (fderiv ℝ f y a₁ + (-(2 * Real.pi * Complex.I) * (ℓ₁ y : ℂ)) * f y)) →
    ℓ₂ a₁ - ℓ₁ a₂ < 0 → f = 0 := by
  first | exact @GlobalTheory.WrongSignGauss.vanish | exact GlobalTheory.WrongSignGauss.vanish | (intros; apply GlobalTheory.WrongSignGauss.vanish <;> assumption)
