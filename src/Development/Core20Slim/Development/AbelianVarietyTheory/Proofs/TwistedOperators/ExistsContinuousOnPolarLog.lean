module

public import Mathlib
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousExptPY
public import Formalism.LocalRingCardinality.DataTheta
public import Init.Core
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Commute.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Algebra.Star.SelfAdjoint
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.Real.Star
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Topology.Algebra.ConstMulAction
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Algebra.Star.Real
public import Mathlib.Topology.Algebra.UniformMulAction
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.ContinuousOn
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Algebra
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.Defs
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs
public import Mathlib.Topology.UniformSpace.Matrix

@[expose] public section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory

noncomputable section
namespace GlobalTheory.PolarLogCont

section
open scoped Matrix.Norms.L2Operator ComplexOrder
variable {n : Type} [Fintype n] [DecidableEq n]

def halfLog (g : Matrix n n ℂ) : Matrix n n ℂ := (1 / 2 : ℝ) • CFC.log (gᴴ * g)

theorem continuousOn_halfLog : ContinuousOn (halfLog (n := n)) {g | IsUnit g} := by
  have h : ContinuousOn (fun g : Matrix n n ℂ => CFC.log (gᴴ * g)) {g | IsUnit g} := by
    refine CFC.continuousOn_log.comp (by fun_prop) ?_
    intro g hg
    have hu : IsUnit g := hg
    refine ⟨?_, ?_⟩
    · show star (gᴴ * g) = gᴴ * g
      rw [star_eq_conjTranspose, conjTranspose_mul, conjTranspose_conjTranspose]
    · exact (show IsUnit gᴴ from hu.star).mul hu
  exact h.const_smul (1 / 2 : ℝ)

theorem halfLog_mul_exp (c Y : Matrix n n ℂ) (hc : cᴴ * c = 1) (hY : Yᴴ = Y) :
    halfLog (c * NormedSpace.exp Y) = Y := by
  have he : (NormedSpace.exp Y)ᴴ = NormedSpace.exp Y := by
    rw [← Matrix.exp_conjTranspose, hY]
  have h2 : NormedSpace.exp (Y + Y) = NormedSpace.exp Y * NormedSpace.exp Y :=
    Matrix.exp_add_of_commute _ _ (Commute.refl Y)
  have sq : (c * NormedSpace.exp Y)ᴴ * (c * NormedSpace.exp Y) = NormedSpace.exp (Y + Y) := by
    rw [conjTranspose_mul, he, h2]
    calc NormedSpace.exp Y * cᴴ * (c * NormedSpace.exp Y)
        = NormedSpace.exp Y * (cᴴ * c) * NormedSpace.exp Y := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hc, Matrix.mul_one]
  have hsa : IsSelfAdjoint (Y + Y) := by
    rw [IsSelfAdjoint, star_eq_conjTranspose, conjTranspose_add, hY]
  unfold halfLog
  rw [sq, CFC.log_exp _ hsa, ← two_smul ℝ Y, smul_smul]
  norm_num

end

theorem exists_continuousOn_polar_log : ∀ (p q : ℕ), ∃ L : Mat p q → (Fin p → Fin q → ℂ), ContinuousOn L {g | IsUnit g} ∧ ∀ (k : Mat p q) (B : Fin p → Fin q → ℂ), kᴴ * k = 1 → L (k * NormedSpace.exp (pY B)) = B := by
  intro p q
  refine ⟨fun g i j => halfLog g (Sum.inl i) (Sum.inr j), ?_, ?_⟩
  · have hc : Continuous fun (M : Mat p q) (i : Fin p) (j : Fin q) => M (Sum.inl i) (Sum.inr j) := by
      fun_prop
    exact hc.comp_continuousOn continuousOn_halfLog
  · intro k B hk
    funext i j
    show halfLog (k * NormedSpace.exp (pY B)) (Sum.inl i) (Sum.inr j) = B i j
    rw [halfLog_mul_exp k _ hk (pY_conjTranspose B)]
    simp [pY, pOf]

end GlobalTheory.PolarLogCont
