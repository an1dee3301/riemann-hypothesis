module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChLApply
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousCharactersLocallyConstantNonarchLocalF
public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Init.Classical
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
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
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Basis
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Support
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.LocallyConstant.Basic

@[expose] public section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData

namespace GlobalTheory.PartRed

theorem sb_mul_addChar_linear : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ∀ (R Q : Type) [Fintype R] [Fintype Q] (f : Matrix R Q k →ₗ[k] k) (z : k) (Φ : Matrix R Q k → ℂ), Φ ∈ SB (Matrix R Q k) → (fun x => (ψ (f x + z) : ℂ) * Φ x) ∈ SB (Matrix R Q k) := by
  intro k _ _ _ _ ψ hψ R Q _ _ f z Φ hΦ
  classical
  obtain ⟨h1, h2⟩ := hΦ
  have hexp : ∀ x : Matrix R Q k, f x = ∑ i, ∑ j, x i j * f (Matrix.single i j 1) := by
    intro x
    conv_lhs => rw [Matrix.matrix_eq_sum_single x]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [← smul_eq_mul, ← LinearMap.map_smul, Matrix.smul_single, smul_eq_mul, mul_one]
  have hf : Continuous f := by
    have : (f : Matrix R Q k → k) = fun x => ∑ i, ∑ j, x i j * f (Matrix.single i j 1) := funext hexp
    rw [this]
    exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
      (continuous_id.matrix_elem i j).mul continuous_const
  refine ⟨?_, ?_⟩
  · exact ((OpenKernel.isLocallyConstant_coe_addChar ψ hψ).comp_continuous
      (hf.add continuous_const)).mul h1
  · exact h2.mul_left

end GlobalTheory.PartRed
