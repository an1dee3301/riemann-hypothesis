module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.EventuallyIteratedFDerivEqZeroOfRealSubspace
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.IsApply
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Torsion.Free
public import Mathlib.Algebra.NoZeroSMulDivisors.Basic
public import Mathlib.Algebra.NoZeroSMulDivisors.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Linear
public import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.Order.Filter.Basic
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.RestrictScalars
public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.Algebra.UniformMulAction
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.MetricSpace.Algebra
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Metrizable.Basic
public import Mathlib.Topology.Metrizable.Uniformity
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

open Filter Topology Set
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.LVs.HolD

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem line2 {H : E → V} {y w : E} {m : E →L[ℂ] E} (hfd : DifferentiableAt ℂ (fderiv ℂ H) y)
    (hz : ∀ t : ℝ, fderiv ℂ H (y + (t : ℂ) • w) (m (y + (t : ℂ) • w)) = 0) :
    fderiv ℂ (fderiv ℂ H) y w (m y) + fderiv ℂ H y (m w) = 0 := by
  have hψ : HasFDerivAt (fun z => fderiv ℂ H z (m z))
      ((fderiv ℂ H y).comp m + (fderiv ℂ (fderiv ℂ H) y).flip (m y)) y :=
    hfd.hasFDerivAt.clm_apply m.hasFDerivAt
  have h := GlobalTheory.SCV.fderiv_apply_eq_zero_of_frequently hψ.differentiableAt (s := w)
    (GlobalTheory.SCV.frequently_nhdsNE_of_eventually_ofReal
      (p := fun t : ℂ => fderiv ℂ H (y + t • w) (m (y + t • w)) = fderiv ℂ H y (m y))
      (Eventually.of_forall fun t => by
        have h0 := hz 0
        simp only [Complex.ofReal_zero, zero_smul, add_zero] at h0
        rw [hz t, h0]))
  rw [hψ.fderiv] at h
  simpa [add_comm] using h

theorem scalar_dir {H : E → V} {y : E} (hd : DifferentiableAt ℂ H y)
    (h : ∀ t : ℝ, H (Complex.exp ((t : ℂ) * Complex.I) • y) = 0) : fderiv ℂ H y y = 0 := by
  have hγ := (((hasDerivAt_id (0 : ℝ)).ofReal_comp.mul_const Complex.I).cexp).smul_const y
  have hc := HasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) (hd.hasFDerivAt.restrictScalars ℝ) hγ (by simp)
  have hc0 := hc.congr_of_eventuallyEq (f₁ := fun _ : ℝ => (0 : V)) (Eventually.of_forall fun t => (h t).symm)
  have := hc0.unique (hasDerivAt_const (0 : ℝ) (0 : V))
  simp only [ContinuousLinearMap.coe_restrictScalars', id, Complex.ofReal_zero, zero_mul, Complex.exp_zero,
    one_mul, map_smul, Complex.ofReal_one] at this
  exact (smul_eq_zero.mp this).resolve_left Complex.I_ne_zero

end PositivityTheory.Rg.Sw.LVs.HolD
