module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralSeriesOfCommonDivisorLineProducts
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.PairingDivisors.StatementH
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddThetaFunctionExistenceUniqueness
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableSqTh
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.Normed.Field.Instances
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Logic.Basic
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.UniformField
public import Mathlib.Topology.Algebra.UniformRing
public import Mathlib.Topology.Algebra.Valued.ValuationTopology
public import Mathlib.Topology.Algebra.Valued.ValuedField
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_series_of_common_divisor_line_products : ∀ (p : ℕ) [Fact p.Prime] (m n : ℕ) (e Ψ A B : PowerSeries ℂ_[p]) (y : Fin m → ℂ_[p]) (y' : Fin n → ℂ_[p]), BddSer e → BddSer Ψ → BddSer A → BddSer B → PowerSeries.constantCoeff Ψ = 1 → Ψ * A = (∏ i, lineSer e (y i)) ^ 2 → Ψ * B = ∏ j, lineSer e (y' j) → (∀ i j, y i ≠ y' j) → IntSer Ψ := by
  first | exact @GlobalTheory.EvenTheta.intSer_of_common_divisor | exact GlobalTheory.EvenTheta.intSer_of_common_divisor | (intros; apply GlobalTheory.EvenTheta.intSer_of_common_divisor <;> assumption)
