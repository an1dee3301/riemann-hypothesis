module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FoundationProofs.LogFactorialPowMulFactorialPowLe
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSelfDualE
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.PairingNondegenerateHolds
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkPderivBlockEmbNe
public import Formalism.GradedWeylDivisibility.StatementE
public import Formalism.HarderNarasimhan.ShiftInvariance
public import Formalism.QuotientMetricDivisors.ReductionLemmaZero
public import Formalism.QuotientMetricDivisors.ProdFormula
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.MeanMaxLeaf.LeafMMFree
public import Init.Data.Cast
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Nat.Init

@[expose] public section

open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_factorial_pow_mul_factorial_pow_le' : ∀ (n R₀ : ℕ) (R : ℝ), 1 ≤ R → (R₀ : ℝ) ≤ R → Real.log (((n.factorial) ^ (2 * R₀) * (R₀.factorial) ^ n : ℕ) : ℝ) ≤ 4 * (n : ℝ) * R * Real.log (n * R) := by
  first | exact @GlobalTheory.log_factorial_pow_mul_factorial_pow_le | exact GlobalTheory.log_factorial_pow_mul_factorial_pow_le | (intros; apply GlobalTheory.log_factorial_pow_mul_factorial_pow_le <;> assumption)
