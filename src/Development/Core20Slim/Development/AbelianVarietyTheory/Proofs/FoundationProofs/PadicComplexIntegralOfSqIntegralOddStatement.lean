module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicComplexIntegralOfSqIntegralOdd
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.PairingDivisors.StatementH
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableSqTh
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.Normed.Field.Instances
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Logic.Basic
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.Topology.Algebra.UniformField
public import Mathlib.Topology.Algebra.UniformRing
public import Mathlib.Topology.Algebra.Valued.ValuationTopology
public import Mathlib.Topology.Algebra.Valued.ValuedField

@[expose] public section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.padicComplex_integral_of_sq_integral_odd : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ H : PowerSeries ℂ_[p], PowerSeries.constantCoeff H = 1 → IntSer (H ^ 2) → IntSer H := by
  first | exact @GlobalTheory.EvenTheta.intSer_of_sq_main | exact GlobalTheory.EvenTheta.intSer_of_sq_main | (intros; apply GlobalTheory.EvenTheta.intSer_of_sq_main <;> assumption)
