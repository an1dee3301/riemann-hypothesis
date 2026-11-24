module

public import Mathlib
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousExptPY
public import Init.Core
public import Init.Data.Function
public import Init.Data.Int.Basic
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Filter.Tendsto
public import Mathlib.Order.Interval.Set.UnorderedInterval
public import Mathlib.Order.Notation
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Topology.Algebra.ConstMulAction
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Algebra.UniformMulAction
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.MetricSpace.Algebra
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.NhdsWithin
public import Mathlib.Topology.UniformSpace.Cauchy
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory

namespace GlobalTheory

theorem hasDerivAt_exp_add_smul_duhamel (A : Type) [NormedRing A] [NormedAlgebra ℝ A]
    [CompleteSpace A] (X V : A) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp (X + t • V))
      (∫ s in (0 : ℝ)..1, NormedSpace.exp ((1 - s) • X) * V * NormedSpace.exp (s • X)) 0 := by
  letI : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A
  have hc : Continuous (NormedSpace.exp : A → A) := NormedSpace.exp_continuous
  set f : ℝ → ℝ → A := fun t s =>
    NormedSpace.exp ((1 - s) • X) * V * NormedSpace.exp (s • (X + t • V)) with hf
  have hfc : Continuous (Function.uncurry f) := by
    simp only [hf, Function.uncurry_def]
    exact ((hc.comp (by fun_prop)).mul continuous_const).mul (hc.comp (by fun_prop))
  set F : ℝ → A := fun t => ∫ s in (0 : ℝ)..1, f t s with hF
  have hFc : Continuous F :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hfc 0 1
  have key : ∀ t : ℝ, NormedSpace.exp (X + t • V) = NormedSpace.exp X + t • F t := by
    intro t
    have hd : ∀ s : ℝ, HasDerivAt
        (fun s : ℝ => NormedSpace.exp ((1 - s) • X) * NormedSpace.exp (s • (X + t • V)))
        (t • f t s) s := by
      intro s
      have h0 : HasDerivAt (fun s : ℝ => 1 - s) (-1) s := by
        simpa using (hasDerivAt_id s).const_sub 1
      have h1 := (hasDerivAt_exp_smul_const (𝕂 := ℝ) X (1 - s)).scomp s h0
      have h2 := hasDerivAt_exp_smul_const' (𝕂 := ℝ) (X + t • V) s
      have h3 := h1.mul h2
      refine h3.congr_deriv ?_
      simp only [hf, Function.comp_apply, neg_smul, one_smul, add_mul, mul_add, mul_assoc,
        neg_mul, smul_mul_assoc, mul_smul_comm]
      abel
    have hi : IntervalIntegrable (fun s => t • f t s) volume 0 1 :=
      ((hfc.comp (Continuous.prodMk_right t)).const_smul t).intervalIntegrable 0 1
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd s) hi
    rw [intervalIntegral.integral_smul] at h
    simp only [sub_self, zero_smul, NormedSpace.exp_zero, one_mul, one_smul, sub_zero,
      mul_one] at h
    simp only [hF]
    rw [h]
    abel
  have hF0 : F 0 = ∫ s in (0 : ℝ)..1,
      NormedSpace.exp ((1 - s) • X) * V * NormedSpace.exp (s • X) := by
    simp [hF, hf]
  rw [← hF0, hasDerivAt_iff_tendsto_slope_zero]
  have ht : Filter.Tendsto F (nhdsWithin 0 {0}ᶜ) (nhds (F 0)) :=
    hFc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  refine ht.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht0
  have ht0' : t ≠ 0 := ht0
  rw [key (0 + t), key 0]
  simp [smul_smul, inv_mul_cancel₀ ht0']

end GlobalTheory
