module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeanLogPeriodConjugatesEqChowlaSelberg
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.PairingDivisors.StatementH
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Data.Cast
public import Init.Data.Nat.Basic
public import Init.Data.Rat.Basic
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.CharP.IntermediateField
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Rat
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.FieldTheory.Minpoly.Field
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal

@[expose] public section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mean_log_period_conjugates_eq_chowlaSelberg : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M], g2 (lamOf D cc δ) ∈ M → g3 (lamOf D cc δ) ∈ M → (∑ ρ : M →ₐ[ℚ] ℂ, Real.log (area (lamConj M ρ (lamOf D cc δ)) / Real.pi)) / (Module.finrank ℚ M : ℝ) = Real.eulerMascheroniConstant + Real.log (2 * Real.pi / Real.sqrt D.host.d) - logDerivativeAtOne D := by
  first | exact @GlobalTheory.PeriodMean.mean_log_period | exact GlobalTheory.PeriodMean.mean_log_period | (intros; apply GlobalTheory.PeriodMean.mean_log_period <;> assumption)
