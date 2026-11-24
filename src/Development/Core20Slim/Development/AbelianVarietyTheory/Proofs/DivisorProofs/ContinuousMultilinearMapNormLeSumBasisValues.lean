module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsContOnOfLocal
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdeleJoinZero
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Module.Multilinear.Basic
public import Mathlib.Analysis.Normed.MulAction
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Finsupp.SMul
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Algebra.Module.Equiv.Basic
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Algebra.Module.Multilinear.Basic
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.MetricSpace.Algebra
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Metrizable.Basic
public import Mathlib.Topology.Metrizable.Uniformity
public import Mathlib.Topology.UniformSpace.Defs
public import Mathlib.Topology.UniformSpace.Real

@[expose] public section

open IsDedekindDomain NumberField
open scoped Classical

theorem GlobalTheory.continuousMultilinear_norm_le_basis_sum : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (ι : Type) [Fintype ι] (b : Module.Basis ι ℝ E) (j : ℕ),
    ∃ K : ℝ, 0 ≤ K ∧ ∀ M : ContinuousMultilinearMap ℝ (fun _ : Fin j => E) ℂ,
      ‖M‖ ≤ K * ∑ cs : Fin j → ι, ‖M (fun r => b (cs r))‖ := by
  intro E _ _ ι _ b j
  haveI : FiniteDimensional ℝ E := Module.Finite.of_basis b
  set C := ‖(b.equivFunL : E →L[ℝ] (ι → ℝ))‖ with hC
  have hC0 : 0 ≤ C := norm_nonneg _
  have hcoord : ∀ (x : E) (c : ι), ‖b.repr x c‖ ≤ C * ‖x‖ := by
    intro x c
    have h1 : b.repr x c = (b.equivFunL : E →L[ℝ] (ι → ℝ)) x c := rfl
    rw [h1]
    exact (norm_le_pi_norm _ c).trans ((b.equivFunL : E →L[ℝ] (ι → ℝ)).le_opNorm x)
  refine ⟨C ^ j, pow_nonneg hC0 _, fun M => ?_⟩
  apply ContinuousMultilinearMap.opNorm_le_bound
  · exact mul_nonneg (pow_nonneg hC0 _) (Finset.sum_nonneg fun _ _ => norm_nonneg _)
  intro v
  have hv : v = fun r => ∑ c, b.repr (v r) c • b c := funext fun r => (b.sum_repr (v r)).symm
  have key : M v = ∑ cs : Fin j → ι, (∏ r, b.repr (v r) (cs r)) • M (fun r => b (cs r)) := by
    conv_lhs => rw [hv]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [M.map_sum]
    refine Finset.sum_congr rfl fun cs _ => ?_
    exact M.map_smul_univ (fun r => b.repr (v r) (cs r)) (fun r => b (cs r))
  rw [key]
  calc ‖∑ cs : Fin j → ι, (∏ r, b.repr (v r) (cs r)) • M (fun r => b (cs r))‖
      ≤ ∑ cs : Fin j → ι, ‖(∏ r, b.repr (v r) (cs r)) • M (fun r => b (cs r))‖ := norm_sum_le _ _
    _ ≤ ∑ cs : Fin j → ι, (C ^ j * ∏ r, ‖v r‖) * ‖M (fun r => b (cs r))‖ := by
      refine Finset.sum_le_sum fun cs _ => ?_
      rw [norm_smul]
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      rw [norm_prod, ← Fin.prod_const, ← Finset.prod_mul_distrib]
      exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun r _ => hcoord (v r) (cs r)
    _ = C ^ j * (∑ cs : Fin j → ι, ‖M (fun r => b (cs r))‖) * ∏ r, ‖v r‖ := by
      rw [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun cs _ => ?_
      ring
