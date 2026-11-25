module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogBranchingConstantSqLe
public import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
public import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.FiniteDimensionalNablaSq
public import Formalism.LocalRingCardinality.DataCoeff
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init

@[expose] public section

open Formalism.BasicNotions

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_branching_constant_sq_le : ∀ {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) (B : ℝ), 1 ≤ B → (N : ℝ) ≤ B → (∀ i, |((lam.w i : ℤ) : ℝ)| ≤ B) → Real.log (Formalism.MainNotions.PrimeDegreeVariant.brBd h lam sg ^ 2) ≤ 5 * N * B * Real.log (6 * B) := by
  first | exact @GlobalTheory.BranchBound.log_brBd_sq_le | exact GlobalTheory.BranchBound.log_brBd_sq_le | (intros; apply GlobalTheory.BranchBound.log_brBd_sq_le <;> assumption)
