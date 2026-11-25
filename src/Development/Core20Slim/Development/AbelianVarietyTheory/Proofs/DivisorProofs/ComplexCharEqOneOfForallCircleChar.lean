module

public import Mathlib
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.UnitBall
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Topology.ContinuousMap.Defs
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

namespace GlobalTheory

noncomputable def circArgChar {G : Type} [Group G] (ν : G →* ℂˣ) : G →* Circle where
  toFun g := ⟨(ν g : ℂ) / (‖(ν g : ℂ)‖ : ℂ), by
    have h : ‖(ν g : ℂ)‖ ≠ 0 := norm_ne_zero_iff.mpr (ν g).ne_zero
    simp [Submonoid.unitSphere, h]⟩
  map_one' := by
    apply Circle.ext
    simp
  map_mul' a b := by
    apply Circle.ext
    show ((ν (a * b) : ℂˣ) : ℂ) / (‖((ν (a * b) : ℂˣ) : ℂ)‖ : ℂ) =
      ((ν a : ℂ) / (‖(ν a : ℂ)‖ : ℂ)) * ((ν b : ℂ) / (‖(ν b : ℂ)‖ : ℂ))
    rw [ν.map_mul, Units.val_mul, norm_mul, Complex.ofReal_mul, mul_div_mul_comm]

noncomputable def circNormChar {G : Type} [Group G] (ν : G →* ℂˣ) (t : ℝ) : G →* Circle where
  toFun g := Circle.exp (t * Real.log ‖(ν g : ℂ)‖)
  map_one' := by simp
  map_mul' a b := by
    have ha : ‖(ν a : ℂ)‖ ≠ 0 := norm_ne_zero_iff.mpr (ν a).ne_zero
    have hb : ‖(ν b : ℂ)‖ ≠ 0 := norm_ne_zero_iff.mpr (ν b).ne_zero
    show Circle.exp (t * Real.log ‖((ν (a * b) : ℂˣ) : ℂ)‖) = _
    rw [ν.map_mul, Units.val_mul, norm_mul, Real.log_mul ha hb, mul_add, Circle.exp_add]

private theorem coe_circArgChar_eq_div_norm {G : Type} [Group G] (ν : G →* ℂˣ) (g : G) :
    ((circArgChar ν g : Circle) : ℂ) = (ν g : ℂ) / (‖(ν g : ℂ)‖ : ℂ) := by
  rfl

theorem complexChar_eq_one_of_forall_circleChar :
    ∀ {G : Type} [Group G] (ν : G →* ℂˣ) (x : G),
      (∀ μ : G →* Circle, (∀ g, ν g = 1 → μ g = 1) → μ x = 1) → ν x = 1 := by
  intro G _ ν x h
  have hx0 : (ν x : ℂ) ≠ 0 := (ν x).ne_zero
  have hpos : 0 < ‖(ν x : ℂ)‖ := norm_pos_iff.mpr hx0

  have hn : ‖(ν x : ℂ)‖ = 1 := by
    by_contra hne
    have hlog : Real.log ‖(ν x : ℂ)‖ ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one hpos hne
    have h2 := h (circNormChar ν (Real.pi / Real.log ‖(ν x : ℂ)‖)) (fun g hg => by
      simp [circNormChar, hg])
    have h3 := congrArg (fun z : Circle => (z : ℂ)) h2
    simp only [circNormChar, MonoidHom.coe_mk, OneHom.coe_mk, Circle.coe_exp,
      div_mul_cancel₀ _ hlog, Circle.coe_one] at h3
    norm_num [Complex.exp_pi_mul_I] at h3

  have h1 := h (circArgChar ν) (fun g hg => by
    apply Circle.ext
    rw [coe_circArgChar_eq_div_norm, hg]
    simp)
  have h4 := congrArg (fun z : Circle => (z : ℂ)) h1
  simp only [coe_circArgChar_eq_div_norm, Circle.coe_one, hn, Complex.ofReal_one, div_one] at h4
  apply Units.ext
  simpa using h4

end GlobalTheory
