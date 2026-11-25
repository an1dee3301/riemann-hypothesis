module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartanDoubleCosetFiniteDisjointLeftCosets
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
public import Development.Core20Slim.Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ScaledIntegerPeriodic
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EventuallyDeepSubset
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Set.BooleanAlgebra
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Pairwise.Basic
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.Order.CompleteBooleanAlgebra
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Order.SetNotation
public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
public import Mathlib.Topology.Defs.Basic

@[expose] public section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.KSplit
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instMeasMat
open GlobalTheory.IndefiniteRowSideFullHecke.ScaledIntegerPeriodic

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cartanDoubleCoset_finite_disjoint_leftCosets : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ϖ : kˣ) (a : ℕ) (n : Fin a → ℤ), ∃ t : Finset (GL (Fin a) k), (∀ x ∈ t, x ∈ KO k (Fin a)) ∧
      shellSet ϖ n = ⋃ x ∈ t, {g : GL (Fin a) k | (x * diagGL (fun i => ϖ ^ n i))⁻¹ * g ∈ KO k (Fin a)} ∧
      (t : Set (GL (Fin a) k)).PairwiseDisjoint
        (fun x => {g : GL (Fin a) k | (x * diagGL (fun i => ϖ ^ n i))⁻¹ * g ∈ KO k (Fin a)}) := by
  first | exact @GlobalTheory.ShellCosets.shell_cosets | exact GlobalTheory.ShellCosets.shell_cosets | (intros; apply GlobalTheory.ShellCosets.shell_cosets <;> assumption)
