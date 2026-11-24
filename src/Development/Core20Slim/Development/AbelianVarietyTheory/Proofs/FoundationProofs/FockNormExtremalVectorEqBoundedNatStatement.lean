module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FoundationProofs.FockNormExtremalVectorEqBoundedNat
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSelfDualE
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.PairingNondegenerateHolds
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkPderivBlockEmbNe
public import Formalism.GradedWeylDivisibility.StatementE
public import Formalism.HarderNarasimhan.ShiftInvariance
public import Formalism.QuotientMetricDivisors.ReductionLemmaZero
public import Formalism.QuotientMetricDivisors.ProdFormula
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.MeanMaxLeaf.LeafMMFree
public import Formalism.LocalRingCardinality.DataCoeff
public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Init.Core
public import Init.Data.Cast
public import Init.Prelude
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Factorial.Basic

@[expose] public section

open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockNorm_extremal_vector_eq_bounded_nat : ∀ (n : ℕ) (lam : DomWeight n) (R : ℕ), (∀ i, lam.natW i ≤ R) → ∃ s : ℕ, 0 < s ∧ s ≤ (n.factorial) ^ (2 * R) * (R.factorial) ^ n ∧ ∀ (K : Type) [Field K] [StarRing K] [CharZero K], fockS (extremal K n lam) (extremal K n lam) = (s : K) := by
  first | exact @GlobalTheory.ExtremalNorm.fockS_extremal_eq_nat | exact GlobalTheory.ExtremalNorm.fockS_extremal_eq_nat | (intros; apply GlobalTheory.ExtremalNorm.fockS_extremal_eq_nat <;> assumption)
