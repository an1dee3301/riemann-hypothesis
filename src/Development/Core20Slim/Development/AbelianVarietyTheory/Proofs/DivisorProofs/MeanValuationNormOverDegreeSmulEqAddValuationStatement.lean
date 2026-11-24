module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeanValuationNormOverDegreeSmulEqAddValuation
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Formalism.PairingDivisors.StatementH
public import Formalism.QuotientMetricDivisors.Statement
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.NumberTheory.NumberField.Basic

@[expose] public section

open NumberField Polynomial IsDedekindDomain
open Formalism.DivisionValues (vw lw)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.meanValuationNormOverDegree_smul_eq_add_valuation : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (σ : K →+* ℂ) (β : ℂ) (u : K) (p q : K[X]), GlobalTheory.FunObj.SqNum.IsMinPol σ β p → GlobalTheory.FunObj.SqNum.IsMinPol σ (σ u * β) q → β ≠ 0 → u ≠ 0 → ∀ w : Formalism.PairingDivisionLocalBalance.Pl K, GlobalTheory.FunObj.SqNum.meanVal_vw w q = GlobalTheory.FunObj.SqNum.meanVal_vw w p + vw w u := by
  first | exact @GlobalTheory.FunObj.SqNum.meanVal_vw_smul | exact GlobalTheory.FunObj.SqNum.meanVal_vw_smul | (intros; apply GlobalTheory.FunObj.SqNum.meanVal_vw_smul <;> assumption)
