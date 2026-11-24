module

public import Mathlib
public import Development.Core20Slim.Formalism.PeriodIntegrals.LatDefs
public import Development.Core20Slim.Formalism.PeriodIntegrals.SigmaStarEx
public import Init.Core
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable

@[expose] public section

noncomputable section

open Complex

namespace PI.SSE

def th (τ u : ℂ) : ℂ := cexp (Real.pi * I * u) * jacobiTheta₂ (u + (1 / 2 + τ / 2)) τ

def ThetaDerivNe : Prop :=
  ∀ τ : ℂ, 0 < τ.im → 3 ≤ 4 * τ.im ^ 2 → jacobiTheta₂' (1 / 2 + τ / 2) τ ≠ 0

def ReduceBasis : Prop :=
  ∀ w₁ w₂ : ℂ, ((starRingEnd ℂ) w₁ * w₂).im ≠ 0 → ∃ v₁ v₂ : ℂ, v₁ ≠ 0 ∧
    PI.lat2 v₁ v₂ = PI.lat2 w₁ w₂ ∧ 0 < (v₂ / v₁).im ∧ 3 ≤ 4 * (v₂ / v₁).im ^ 2

end PI.SSE

end
