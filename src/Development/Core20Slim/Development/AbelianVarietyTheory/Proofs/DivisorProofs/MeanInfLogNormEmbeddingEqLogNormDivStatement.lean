module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeanInfLogNormEmbeddingEqLogNormDiv
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Formalism.PairingDivisors.StatementH
public import Batteries.Classes.RatCast
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.RingTheory.Norm.Defs

@[expose] public section

open NumberField Polynomial IsDedekindDomain
open Formalism.DivisionValues (vw lw)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.meanInf_log_norm_embedding_eq_log_norm_div : ∀ (K : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] (a : K), a ≠ 0 → Formalism.PairingDivisionLocalBalance.meanInf K (fun v => Real.log ‖v.embedding a‖) = Real.log |((Algebra.norm ℚ a : ℚ) : ℝ)| / Module.finrank ℚ K := by
  first | exact @GlobalTheory.meanInf_log_norm_embedding | exact GlobalTheory.meanInf_log_norm_embedding | (intros; apply GlobalTheory.meanInf_log_norm_embedding <;> assumption)
