module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatTensorMovedTensorFinsetSumLinear
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasCompactSupportFlatIntegrand
public import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Init.Prelude
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
public import Mathlib.Topology.Defs.Basic

@[expose] public section

open MeasureTheory GlobalTheory.FunObj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flatTensor_movedTensor_finset_sum_linear : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (G : GlobalTheory.SplitFlip.Grid k) (hs : 1 ≤ G.s) (ψ : AddChar k Circle) (ν : Measure k) [ν.IsAddHaarMeasure], Continuous ψ → ∀ (ϖ : kˣ) (e : ℕ) (keep : Bool) (g : G.VertexGroup) {ι : Type} (S : Finset ι) (x : ι → ℂ) (T : ι → G.Args → ℂ), (∀ i ∈ S, G.IsTensor ϖ e (GlobalTheory.SplitFlip.oppositePath G.m) (T i)) → ∀ X Y, flatTensor hs ψ ν (moved G keep g (fun z => ∑ i ∈ S, x i * T i z)) X Y = ∑ i ∈ S, x i * flatTensor hs ψ ν (moved G keep g (T i)) X Y := by
  first | exact @GlobalTheory.FunObj.flatTensor_moved_sum | exact GlobalTheory.FunObj.flatTensor_moved_sum | (intros; apply GlobalTheory.FunObj.flatTensor_moved_sum <;> assumption)
