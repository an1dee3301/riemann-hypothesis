module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeanValuationGeOfIntegralAtPrime
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.VpBounds
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricSumEqHeckeLValueMulAuxiliaryFactors
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinPartEqOneOfLevel
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsValCharTwist
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeTateFunctionalEquationCM
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLPartialContinuationHolds
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsFinSetSplitPlacesCoprimeConductor
public import Formalism.PairingDivisors.StatementH
public import Formalism.QuotientMetricDivisors.Statement
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Ideal.Defs

@[expose] public section

open NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.meanValuation_ge_of_integral_at_prime : ∀ {K : Type} [Field K] [NumberField K] (σ : K →+* ℂ) {β : ℂ} {p : K[X]}, GlobalTheory.FunObj.SqNum.IsMinPol σ β p → β ≠ 0 → ∀ {c : K}, c ≠ 0 → ∀ {l : ℕ}, l.Prime → ∀ {w : Formalism.PairingDivisionLocalBalance.Pl K}, (l : 𝓞 K) ∈ w.asIdeal → ∀ {m : ℕ}, GlobalTheory.CMVal.IntAt l ((l : ℂ) ^ m * (σ c * β)) → -((m : ℝ) * (Formalism.DivisionValues.vw w (l : K) : ℝ)) ≤ (Formalism.DivisionValues.vw w c : ℝ) + GlobalTheory.FunObj.SqNum.meanVal_vw w p := by
  first | exact @GlobalTheory.FunObj.SqNum.meanVal_vw_ge_of_intAt | exact GlobalTheory.FunObj.SqNum.meanVal_vw_ge_of_intAt | (intros; apply GlobalTheory.FunObj.SqNum.meanVal_vw_ge_of_intAt <;> assumption)
