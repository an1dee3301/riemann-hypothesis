module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicComplexIntegralBoundedSeriesLaws
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.PairingDivisors.StatementH
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddThetaFunctionExistenceUniqueness
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableSqTh
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Instances
public import Mathlib.Analysis.Normed.Group.Completion
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Logic.Basic
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.MvPowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.PowerSeries.Substitution
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.GroupCompletion
public import Mathlib.Topology.Algebra.UniformField
public import Mathlib.Topology.Algebra.UniformRing
public import Mathlib.Topology.Algebra.Valued.ValuationTopology
public import Mathlib.Topology.Algebra.Valued.ValuedField
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.padicComplex_integral_bounded_series_laws : ∀ (p : ℕ) [Fact p.Prime], (∀ f g : PowerSeries ℂ_[p], IntSer f → IntSer g → IntSer (f + g) ∧ IntSer (f - g) ∧ IntSer (f * g)) ∧ (∀ f g : PowerSeries ℂ_[p], BddSer f → BddSer g → BddSer (f + g) ∧ BddSer (f - g) ∧ BddSer (f * g)) ∧ (∀ c : ℂ_[p], BddSer (PowerSeries.C c) ∧ (‖c‖ ≤ 1 → IntSer (PowerSeries.C c))) ∧ IntSer (PowerSeries.X : PowerSeries ℂ_[p]) ∧ (∀ f : PowerSeries ℂ_[p], IntSer f → ‖PowerSeries.constantCoeff f‖ = 1 → IntSer f⁻¹) ∧ (∀ (f h : PowerSeries ℂ_[p]) (B : ℝ), (∀ n, ‖PowerSeries.coeff n f‖ ≤ B) → IntSer h → PowerSeries.constantCoeff h = 0 → ∀ n, ‖PowerSeries.coeff n (PowerSeries.subst h f : PowerSeries ℂ_[p])‖ ≤ B) ∧ ∀ (f g : PowerSeries ℂ_[p]) (A B : ℝ), (∀ n, ‖PowerSeries.coeff n f‖ ≤ A) → (∀ n, ‖PowerSeries.coeff n g‖ ≤ B) → ∀ n, ‖PowerSeries.coeff n (f * g)‖ ≤ A * B := by
  first | exact @GlobalTheory.EvenTheta.SerRing.series_ring_laws | exact GlobalTheory.EvenTheta.SerRing.series_ring_laws | (intros; apply GlobalTheory.EvenTheta.SerRing.series_ring_laws <;> assumption)
