module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.SinhcAdMulVecOfAdSqEigen
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousExptPY
public import Formalism.LocalRingCardinality.DataTheta
public import Init.Core
public import Init.Prelude
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Defs

@[expose] public section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sinhcAd_mulVec_of_adSq_eigen : ∀ (p q : ℕ) (Y : Mat p q) (v : Ix p q × Ix p q → ℂ) (x : ℝ), (adMat Y ^ 2) *ᵥ v = ((x : ℂ) ^ 2) • v → sinhcAd Y *ᵥ v = ((shc x : ℝ) : ℂ) • v := by
  first | exact @GlobalTheory.PolarU.sinhcAd_mulVec_of_sq_eigen | exact GlobalTheory.PolarU.sinhcAd_mulVec_of_sq_eigen | (intros; apply GlobalTheory.PolarU.sinhcAd_mulVec_of_sq_eigen <;> assumption)
