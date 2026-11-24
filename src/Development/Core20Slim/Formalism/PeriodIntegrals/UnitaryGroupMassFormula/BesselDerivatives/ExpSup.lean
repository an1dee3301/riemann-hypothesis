module

public import Mathlib
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Nat.Basic
public import Init.Data.Order.Lemmas
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.WithTop
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.IsEmpty.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.ENat.Basic
public import Mathlib.Data.ENat.Defs
public import Mathlib.Data.ENat.Monoid
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.FieldTheory.Perfect
public import Mathlib.FieldTheory.Separable
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Notation
public import Mathlib.Order.RelClasses
public import Mathlib.Order.TypeTags
public import Mathlib.Order.WithBot
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Algebra
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs
public import Mathlib.Topology.UniformSpace.Real

@[expose] public section

open scoped ContDiff Topology
open Matrix

noncomputable section

namespace PI.BesselDerivW

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

open scoped Matrix.Norms.Operator in
theorem exp_entry_contDiff (X : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    ContDiff ℝ ∞ (fun t : ℝ => (NormedSpace.exp ((t : ℂ) • X)) i j) := by
  have hd : ∀ t : ℝ, HasDerivAt (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X))
      (NormedSpace.exp ((t : ℂ) • X) * X) t := by
    intro t
    have e : (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X)) = fun u : ℝ => NormedSpace.exp (u • X) := by
      funext t; rw [Complex.coe_smul]
    rw [e, Complex.coe_smul]
    exact hasDerivAt_exp_smul_const (𝕂 := ℝ) X t
  set f := fun t : ℝ => NormedSpace.exp ((t : ℂ) • X) with hf
  have hdiff : Differentiable ℝ f := fun t => (hd t).differentiableAt
  have hder : deriv f = fun t => f t * X := funext fun t => (hd t).deriv
  have hcd : ∀ m : ℕ, ContDiff ℝ m f := by
    intro m
    induction m with
    | zero => exact (contDiff_zero.2 hdiff.continuous).of_le (by simp)
    | succ m ih =>
      have h' : ContDiff ℝ m (deriv f) := by rw [hder]; exact ih.mul contDiff_const
      have h1 : ContDiff ℝ ((m : WithTop ℕ∞) + 1) f := by
        first
        | exact contDiff_succ_iff_deriv.2 ⟨hdiff, by simp, h'⟩
        | exact contDiff_succ_iff_deriv.2 ⟨hdiff, h'⟩
      exact h1.of_le (by norm_num)
  have hcf : ContDiff ℝ ∞ f := contDiff_infty.2 hcd
  let L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] ℂ :=
    { toFun := fun M => M i j, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  exact (LinearMap.toContinuousLinearMap L).contDiff.comp hcf

theorem exp_contDiff (X : Matrix (Fin n) (Fin n) ℂ) :
    ContDiff ℝ ∞ (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X)) := by
  refine contDiff_pi.2 fun i => contDiff_pi.2 fun j => ?_
  exact exp_entry_contDiff X i j



end PI.BesselDerivW
