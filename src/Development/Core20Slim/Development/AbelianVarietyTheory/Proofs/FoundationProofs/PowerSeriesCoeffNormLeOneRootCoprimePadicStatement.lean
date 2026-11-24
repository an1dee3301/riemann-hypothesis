module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FoundationProofs.PowerSeriesCoeffNormLeOneRootCoprimePadic
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableSqTh
public import Init.Data.Nat.Coprime
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

open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.powerSeriesCoeffNormLeOne_root_coprime_padic : ∀ (p : ℕ) [Fact p.Prime] (N : ℕ), 0 < N → Nat.Coprime N p →
    ∀ s : PowerSeries ℂ_[p], PowerSeries.constantCoeff s = 1 →
      GlobalTheory.EvenTheta.IntSer (s ^ N) → GlobalTheory.EvenTheta.IntSer s := by
  first | exact @GlobalTheory.RootInt.intSer_root | exact GlobalTheory.RootInt.intSer_root | (intros; apply GlobalTheory.RootInt.intSer_root <;> assumption)
