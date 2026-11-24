module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogCmConstantAddLogDerivativeLeSquareTopBound
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.AbelianVarietyTheory.Definitions.Divisors.EntireEqOfHalfPlane
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataParams₂
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.PairingDivisors.StatementH
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init

@[expose] public section

open GlobalTheory.SqTop GlobalTheory.FunObj.SqNum GlobalTheory.CMVal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_cmConstant_add_logDerivative_le_squareTopBound : ∀ ε : ℝ, ∃ Cx x₁ : ℝ, ∀ (D : Formalism.BasicNotions.D7) (large₂ : Formalism.BasicNotions.SizeData₂ D), large₂.sc.eps = ε → x₁ ≤ large₂.sc.x → Rec large₂ → ∀ (i j : Fin D.R.m) (s : ℕ), 1 ≤ s → s ≤ halfRank D i j → Real.log (C0 D.host.E D.host.d (2 * s) (kap D 1 i j s)) + (Formalism.PairingDivisionLocalBalance.wtM (2 * s) (kap D 1 i j s) : ℝ) * ((Real.log D.host.d + |large₂.logDerivativeAtOne|) / 2) ≤ bTH D Cx large₂.sc.x large₂.sc.b := by
  first | exact @GlobalTheory.SizesArch.sizes | exact GlobalTheory.SizesArch.sizes | (intros; apply GlobalTheory.SizesArch.sizes <;> assumption)
