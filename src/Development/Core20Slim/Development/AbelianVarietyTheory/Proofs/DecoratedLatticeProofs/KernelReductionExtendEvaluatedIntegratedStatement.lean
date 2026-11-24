module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.KernelReductionExtendEvaluatedIntegrated
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsRead
public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.UnitBall
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Empty
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Basis
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Disjoint
public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Instances.Matrix

@[expose] public section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernelReduction_extend_evaluated_integrated : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ψ ≠ 1 → ν.IsAddHaarMeasure → ∀ (m m' : Type) [Fintype m] [DecidableEq m] [Fintype m'] [DecidableEq m'] (M : Type) [AddCommGroup M] [Module ℂ M] (l : SB (Matrix m m' k) →ₗ[ℂ] M) (β : Matrix m m' k) (ev it ev' it' : Finset (m × m')), ev ⊆ ev' → it ⊆ it' → Disjoint ev' it' → GlobalTheory.FlatFactor.KerRed ν ev it β l → (∀ e ∈ ev', e ∉ ev → ∀ (b : k) (Θ Θ' : SB (Matrix m m' k)), (∀ t, Θ'.1 t = (ψ (b * (t e.1 e.2 - β e.1 e.2)) : ℂ) * Θ.1 t) → l Θ' = l Θ) → (∀ e ∈ it', e ∉ it → ∀ (a : k) (Θ Θ' : SB (Matrix m m' k)), (∀ t, Θ'.1 t = Θ.1 (t + Matrix.single e.1 e.2 a)) → l Θ' = l Θ) → GlobalTheory.FlatFactor.KerRed ν ev' it' β l := by
  first | exact @GlobalTheory.FlatFactor.KerRedStep.kerRed_extend | exact GlobalTheory.FlatFactor.KerRedStep.kerRed_extend | (intros; apply GlobalTheory.FlatFactor.KerRedStep.kerRed_extend <;> assumption)
