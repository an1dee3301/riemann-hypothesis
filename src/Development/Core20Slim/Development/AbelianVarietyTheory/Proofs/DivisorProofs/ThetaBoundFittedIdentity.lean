module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.SlopeTestRemainingChoicesAlt
public import Development.Core20Slim.Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.Divisors.TieTest
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Development.AbelianVarietyTheory.Definitions.Divisors.LeastSplitAuxiliaryPrimeThetaChainSpec
public import Development.AbelianVarietyTheory.Definitions.Divisors.TwistedPlaceChoiceLiesOverPair
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.PairingDivisors.StatementH
public import Formalism.PairingDivisors.StatementX
public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ValBasic
public import Formalism.QuotientMetricDivisors.Statement
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Notation.Support
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Kleene
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Cast.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Cast.Order.Ring
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SqTop NumberField

namespace GlobalTheory.BigTop.Fun.ThbTie

theorem sqRank_half {D : D7} (ij : Sq D) : sqRank D ij / 2 = GlobalTheory.FunObj.SqNum.halfRank D ij.1 ij.2 := by
  unfold sqRank GlobalTheory.FunObj.SqNum.halfRank GlobalTheory.ChiGrid.rankV
  congr 1
  ring

theorem htLe_nonneg {K : Type} [Field K] [NumberField K] [StarRing K] {g : Formalism.PairingDivisionLocalBalance.Pl K → ℤ} {z : K} {B : ℝ}
    (h : Formalism.PairingDivisionLocalBalance.HtLe g z B) : 0 ≤ B :=
  (finsum_nonneg fun w => mul_nonneg (div_nonneg (Real.log_natCast_nonneg _) (Nat.cast_nonneg _)) (abs_nonneg _)).trans h.2

theorem htLe_one_zero {K : Type} [Field K] [NumberField K] [StarRing K] {B : ℝ} (hB : 0 ≤ B) :
    Formalism.PairingDivisionLocalBalance.HtLe (fun _ => (0 : ℤ)) (1 : K) B := by
  have e : (fun w : Formalism.PairingDivisionLocalBalance.Pl K => Formalism.DivisionValues.lw w * |((Formalism.DivisionValues.vw w (1 : K) + 0 : ℤ) : ℝ)|) = fun _ => 0 := by
    funext w
    simp [Formalism.DivisionValues.ValuationRepresentative.vw_one]
  refine ⟨?_, ?_⟩
  · rw [e]
    simp
  · rw [e, finsum_zero]
    exact hB

end GlobalTheory.BigTop.Fun.ThbTie


end
