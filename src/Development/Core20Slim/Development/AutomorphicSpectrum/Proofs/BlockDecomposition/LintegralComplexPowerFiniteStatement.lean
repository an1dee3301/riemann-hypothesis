module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LintegralComplexPowerFinite
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecondCountableHermC
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousBlkM
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.Order.Notation

@[expose] public section

open MeasureTheory Matrix
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_complex_power_finite : ∀ (n : ℕ) (t : ℝ), (n : ℝ) < t →
    ∫⁻ v : Fin n → ℂ, ENNReal.ofReal ((1 + ∑ i, Complex.normSq (v i)) ^ (-t)) ≠ ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt.lintegral_one_add_normSq_rpow_ne_top | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt.lintegral_one_add_normSq_rpow_ne_top | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt.lintegral_one_add_normSq_rpow_ne_top <;> assumption)
