module

public import Mathlib
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Quotient
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Field.UnitBall
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.ExistsUnique
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.GroupTheory.Coset.Defs
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Lattice
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.Topology.Algebra.GroupWithZero
public import Mathlib.Topology.Algebra.Module.LocallyConvex
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Connected.Basic
public import Mathlib.Topology.Connected.PathConnected
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.ContinuousMap.Defs
public import Mathlib.Topology.Covering.AddCircle
public import Mathlib.Topology.Covering.Basic
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Topology.Instances.RealVectorSpace
public import Mathlib.Topology.Instances.ZMultiples
public import Mathlib.Topology.MetricSpace.Algebra
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Metrizable.Basic
public import Mathlib.Topology.Metrizable.Uniformity
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

namespace GroundTheory.Global

open Complex

theorem isCoveringMap_circleExp : IsCoveringMap (Circle.exp : ℝ → Circle) := by
  have h : IsCoveringMap ((↑) : ℝ → AddCircle (2 * Real.pi)) := AddCircle.isCoveringMap_coe _
  exact h.homeomorph_comp AddCircle.homeomorphCircle'

theorem existsUnique_circleExp_of_continuous (χ : ℝ → Circle) (hχ : Continuous χ)
    (hmul : ∀ s t, χ (s + t) = χ s * χ t) : ∃! τ : ℝ, ∀ t, χ t = Circle.exp (τ * t) := by
  have cov := isCoveringMap_circleExp
  have h0 : χ 0 = 1 := by
    have h := hmul 0 0
    rw [add_zero] at h
    exact mul_left_cancel (a := χ 0) (by rw [mul_one]; exact h.symm)
  obtain ⟨F, ⟨hF0, hF⟩, -⟩ :=
    cov.existsUnique_continuousMap_lifts ⟨χ, hχ⟩ (0 : ℝ) (0 : ℝ) (by simp [h0])
  have hF' : ∀ t, Circle.exp (F t) = χ t := fun t => congrFun hF t
  have hadd : ∀ s t, F (s + t) = F s + F t := by
    intro s
    have key := cov.eq_of_comp_eq (g₁ := fun t => F (s + t) - F s - F t)
      (g₂ := fun _ => (0 : ℝ)) (by fun_prop) continuous_const (by
        funext t
        simp only [Function.comp_apply, Circle.exp_sub, hF', hmul, Circle.exp_zero]
        simp) 0 (by simp [hF0])
    intro t
    have := congrFun key t
    linarith
  have hlin : ∀ t, F t = F 1 * t := by
    intro t
    have := map_real_smul (AddMonoidHom.mk' F hadd) F.continuous t 1
    simpa [mul_comm] using this
  refine ⟨F 1, fun t => by rw [← hlin, hF'], ?_⟩
  intro τ hτ
  have key := cov.eq_of_comp_eq (g₁ := fun t : ℝ => τ * t) (g₂ := fun t => F 1 * t)
    (by fun_prop) (by fun_prop)
    (by funext t; simp only [Function.comp_apply]; rw [← hτ, ← hlin, hF']) 0 (by simp)
  simpa using congrFun key 1

theorem eq_of_forall_exp_mul_eq {s s' : ℂ}
    (h : ∀ t : ℝ, Complex.exp (s * t) = Complex.exp (s' * t)) : s = s' := by
  have hd : ∀ u : ℂ, HasDerivAt (fun t : ℝ => Complex.exp (u * t)) u 0 := by
    intro u
    have := ((hasDerivAt_id (0 : ℝ)).ofReal_comp.const_mul u).cexp
    simpa using this
  have e : (fun t : ℝ => Complex.exp (s * t)) = fun t : ℝ => Complex.exp (s' * t) := funext h
  have h' : HasDerivAt (fun t : ℝ => Complex.exp (s * t)) s' 0 := by rw [e]; exact hd s'
  exact (hd s).unique h'

theorem existsUnique_exp_of_continuous (χ : ℝ → ℂˣ) (hχ : Continuous χ)
    (hmul : ∀ s t, χ (s + t) = χ s * χ t) :
    ∃! s : ℂ, ∀ t : ℝ, (χ t : ℂ) = Complex.exp (s * t) := by
  refine existsUnique_of_exists_of_unique ?_
    (fun s s' hs hs' => eq_of_forall_exp_mul_eq fun t => by rw [← hs, ← hs'])
  have hc : Continuous fun t => (χ t : ℂ) := Units.continuous_val.comp hχ
  have hnpos : ∀ t, 0 < ‖(χ t : ℂ)‖ := fun t => norm_pos_iff.mpr (χ t).ne_zero

  have ℓadd : ∀ s t, Real.log ‖(χ (s + t) : ℂ)‖ =
      Real.log ‖(χ s : ℂ)‖ + Real.log ‖(χ t : ℂ)‖ := by
    intro s t
    rw [hmul, Units.val_mul, norm_mul]
    exact Real.log_mul (hnpos s).ne' (hnpos t).ne'
  have ℓcont : Continuous fun t => Real.log ‖(χ t : ℂ)‖ := hc.norm.log fun t => (hnpos t).ne'
  have ℓlin : ∀ t, Real.log ‖(χ t : ℂ)‖ = Real.log ‖(χ 1 : ℂ)‖ * t := by
    intro t
    have := map_real_smul (AddMonoidHom.mk' (fun t => Real.log ‖(χ t : ℂ)‖) ℓadd) ℓcont t 1
    simpa [mul_comm] using this

  let u : ℝ → Circle := fun t => ⟨(χ t : ℂ) / (‖(χ t : ℂ)‖ : ℂ),
    mem_sphere_zero_iff_norm.2 (by simp [(hnpos t).ne'])⟩
  have ucont : Continuous u := by
    apply Continuous.subtype_mk
    exact hc.div (Complex.continuous_ofReal.comp hc.norm) fun t => by
      exact_mod_cast (hnpos t).ne'
  have umul : ∀ s t, u (s + t) = u s * u t := by
    intro s t
    apply Circle.coe_injective
    rw [Circle.coe_mul]
    show (χ (s + t) : ℂ) / (‖(χ (s + t) : ℂ)‖ : ℂ) =
      (χ s : ℂ) / (‖(χ s : ℂ)‖ : ℂ) * ((χ t : ℂ) / (‖(χ t : ℂ)‖ : ℂ))
    rw [hmul, Units.val_mul, norm_mul, Complex.ofReal_mul, mul_div_mul_comm]
  obtain ⟨τ, hτ, -⟩ := existsUnique_circleExp_of_continuous u ucont umul
  refine ⟨Real.log ‖(χ 1 : ℂ)‖ + τ * I, fun t => ?_⟩
  have h1 : (χ t : ℂ) = (‖(χ t : ℂ)‖ : ℂ) * (u t : ℂ) := by
    show _ = _ * (_ / _)
    rw [mul_div_cancel₀]
    exact_mod_cast (hnpos t).ne'
  have h2 : (‖(χ t : ℂ)‖ : ℂ) = Complex.exp ((Real.log ‖(χ 1 : ℂ)‖ * t : ℝ)) := by
    rw [← ℓlin, ← Complex.ofReal_exp, Real.exp_log (hnpos t)]
  rw [h1, h2, hτ t, Circle.coe_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

end GroundTheory.Global
