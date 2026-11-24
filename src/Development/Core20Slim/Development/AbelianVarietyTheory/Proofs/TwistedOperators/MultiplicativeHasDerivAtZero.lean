module

public import Mathlib
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Inverse
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Module.RCLike.Real
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.Order.Filter.Basic
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.MetricSpace.Algebra
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

namespace GlobalTheory

theorem multiplicative_hasDerivAt_zero : ∀ (lam : ℝ → ℂ), lam 0 = 1 →
    (∀ s t, lam (s + t) = lam s * lam t) → ContinuousAt lam 0 → ∃ c : ℂ, HasDerivAt lam c 0 := by
  intro lam h0 hmul hc
  have hcont : Continuous lam := by
    rw [continuous_iff_continuousAt]
    intro t
    have h1 : ContinuousAt (fun x => lam (x - t)) t := by
      apply ContinuousAt.comp (g := lam) (f := fun x => x - t)
      · simpa using hc
      · exact (continuous_id.sub continuous_const).continuousAt
    have h2 : (fun x => lam t * lam (x - t)) = lam := by
      funext x; rw [← hmul]; congr 1; ring
    rw [← h2]; exact continuousAt_const.mul h1
  set F : ℝ → ℂ := fun u => ∫ x in (0:ℝ)..u, lam x with hF
  have hFd : ∀ b, HasDerivAt F (lam b) b := fun b =>
    (hcont.integral_hasStrictDerivAt 0 b).hasDerivAt
  obtain ⟨δ, hδ⟩ : ∃ δ, F δ ≠ 0 := by
    have := (hFd 0).eventually_ne (c := 0) (by rw [h0]; exact one_ne_zero)
    exact this.exists
  have hi : ∀ a b : ℝ, IntervalIntegrable lam MeasureTheory.volume a b :=
    fun a b => hcont.intervalIntegrable a b
  have key : ∀ t, lam t * F δ = F (t + δ) - F t := by
    intro t
    calc lam t * F δ = ∫ s in (0:ℝ)..δ, lam (t + s) := by
          simp only [hF, hmul]; rw [intervalIntegral.integral_const_mul]
      _ = ∫ s in (t + 0)..(t + δ), lam s := intervalIntegral.integral_comp_add_left lam t
      _ = F (t + δ) - F t := by
          simp only [add_zero, hF]
          exact (intervalIntegral.integral_interval_sub_left (hi 0 (t + δ)) (hi 0 t)).symm
  have hd : HasDerivAt (fun t => (F (t + δ) - F t) * (F δ)⁻¹)
      ((lam (0 + δ) - lam 0) * (F δ)⁻¹) 0 := by
    have h1 : HasDerivAt (fun t => F (t + δ)) (lam (0 + δ)) 0 :=
      HasDerivAt.comp_add_const 0 δ (hFd (0 + δ))
    exact (h1.sub (hFd 0)).mul_const _
  refine ⟨_, hd.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)⟩
  simp only
  rw [← key t, mul_assoc, mul_inv_cancel₀ hδ, mul_one]

end GlobalTheory
