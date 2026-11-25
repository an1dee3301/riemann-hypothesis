module

public import Mathlib
public import Init.Core
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.Monoid.Unbundled.ExistsOfLE
public import Mathlib.Algebra.Order.Ring.Basic
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Order.Lattice
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.Real.ConjExponents
public import Mathlib.Basic.Real.Star
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Lattice
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Order.OrderClosed
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open MeasureTheory

namespace GlobalTheory

theorem norm_integral_star_mul_sq_le {X : Type} [MeasurableSpace X] (μ : Measure X) (f h : X → ℂ)
    (hf : AEStronglyMeasurable f μ) (hh : AEStronglyMeasurable h μ)
    (hff : Integrable (fun x => star (f x) * f x) μ) (hhh : Integrable (fun x => star (h x) * h x) μ) :
    ‖∫ x, star (f x) * h x ∂μ‖ ^ 2 ≤ (∫ x, star (f x) * f x ∂μ).re * (∫ x, star (h x) * h x ∂μ).re := by
  have key : ∀ g : X → ℂ, (fun x => star (g x) * g x) = fun x => ((‖g x‖ ^ 2 : ℝ) : ℂ) := by
    intro g; funext x; rw [Complex.star_def, Complex.conj_mul']; push_cast; rfl
  have re_eq : ∀ g : X → ℂ, (∫ x, star (g x) * g x ∂μ).re = ∫ x, ‖g x‖ ^ 2 ∂μ := by
    intro g; rw [key g, integral_complex_ofReal]; rfl
  have int_sq : ∀ g : X → ℂ, Integrable (fun x => star (g x) * g x) μ → Integrable (fun x => ‖g x‖ ^ 2) μ := by
    intro g hg; rw [key g] at hg; have hr := hg.re; simp only [RCLike.re_to_complex, Complex.ofReal_re] at hr; exact hr
  have mf : MemLp f (ENNReal.ofReal 2) μ := by
    rw [show ENNReal.ofReal 2 = 2 by simp]; exact (memLp_two_iff_integrable_sq_norm hf).mpr (int_sq f hff)
  have mh : MemLp h (ENNReal.ofReal 2) μ := by
    rw [show ENNReal.ofReal 2 = 2 by simp]; exact (memLp_two_iff_integrable_sq_norm hh).mpr (int_sq h hhh)
  have hold := integral_mul_norm_le_Lp_mul_Lq (p := 2) (q := 2) Real.HolderConjugate.two_two mf mh
  simp only [Real.rpow_two] at hold
  rw [re_eq f, re_eq h]
  have A0 : 0 ≤ ∫ x, ‖f x‖ ^ 2 ∂μ := integral_nonneg fun x => by positivity
  have B0 : 0 ≤ ∫ x, ‖h x‖ ^ 2 ∂μ := integral_nonneg fun x => by positivity
  have n1 : ‖∫ x, star (f x) * h x ∂μ‖ ≤ ∫ x, ‖f x‖ * ‖h x‖ ∂μ := by
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    congr 1; funext x; rw [norm_mul, norm_star]
  have n0 : 0 ≤ ‖∫ x, star (f x) * h x ∂μ‖ := norm_nonneg _
  have hsq : ((∫ x, ‖f x‖ ^ 2 ∂μ) ^ (1 / (2:ℝ)) * (∫ x, ‖h x‖ ^ 2 ∂μ) ^ (1 / (2:ℝ))) ^ 2
      = (∫ x, ‖f x‖ ^ 2 ∂μ) * (∫ x, ‖h x‖ ^ 2 ∂μ) := by
    rw [mul_pow, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, Real.sq_sqrt A0, Real.sq_sqrt B0]
  calc ‖∫ x, star (f x) * h x ∂μ‖ ^ 2 ≤ ((∫ x, ‖f x‖ ^ 2 ∂μ) ^ (1 / (2:ℝ)) * (∫ x, ‖h x‖ ^ 2 ∂μ) ^ (1 / (2:ℝ))) ^ 2 :=
        pow_le_pow_left₀ n0 (n1.trans hold) 2
    _ = _ := hsq

end GlobalTheory
