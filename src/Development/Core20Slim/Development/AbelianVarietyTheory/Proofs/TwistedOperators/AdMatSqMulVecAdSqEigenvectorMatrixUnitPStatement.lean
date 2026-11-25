module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdMatSqMulVecAdSqEigenvectorMatrixUnitP
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
theorem _root_.GlobalTheory.T.adMat_sq_mulVec_adSqEigenvectorMatrixUnitP : ∀ (p q : ℕ) (h : ℕ → ℝ) (ab : PIx p q), (adMat (aOf p q h) ^ 2) *ᵥ eigP ab.1 = (((rootP h ab.1 : ℝ) : ℂ) ^ 2) • eigP ab.1 := by
  first | exact @GlobalTheory.PolarU.adMat_sq_mulVec_eigP | exact GlobalTheory.PolarU.adMat_sq_mulVec_eigP | (intros; apply GlobalTheory.PolarU.adMat_sq_mulVec_eigP <;> assumption)
