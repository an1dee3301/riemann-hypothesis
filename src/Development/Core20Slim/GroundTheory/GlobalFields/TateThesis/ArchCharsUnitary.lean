module

public import Mathlib
public import Development.Core20Slim.GroundTheory.GlobalFields.TateThesis.ArchChars
public import Development.Core20Slim.GroundTheory.GlobalFields.TateThesis.ArchCharsUnits
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Positive.Ring
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.UnitBall
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.ExistsUnique
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

namespace GroundTheory.Global

open Complex

theorem re_eq_zero_of_norm_exp_one_cpow {s : ℂ}
    (h : ‖((Real.exp 1 : ℝ) : ℂ) ^ s‖ = 1) : s.re = 0 := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (Real.exp_pos 1), Real.exp_one_rpow] at h
  exact Real.exp_eq_one_iff _ |>.mp h

theorem existsUnique_mul_I_of_re_eq_zero {P : ℂ → Prop} (h : ∃! s, P s)
    (hre : ∀ s, P s → s.re = 0) : ∃! τ : ℝ, P ((τ : ℂ) * I) := by
  obtain ⟨s, hs, hu⟩ := h
  have hs' : s = (s.im : ℂ) * I := by
    apply Complex.ext <;> simp [hre s hs]
  refine ⟨s.im, by show P ((s.im : ℂ) * I); rw [← hs']; exact hs, fun τ hτ => ?_⟩
  have := congrArg Complex.im (hu _ hτ)
  simpa using this


theorem existsUnique_cpow_of_pos_circle (χ : {x : ℝ // 0 < x} →ₜ* Circle) :
    ∃! τ : ℝ, ∀ x : {x : ℝ // 0 < x}, (χ x : ℂ) = ((x : ℝ) : ℂ) ^ ((τ : ℂ) * I) := by
  apply existsUnique_mul_I_of_re_eq_zero (existsUnique_cpow_of_pos (circleToUnits.comp χ))
  intro s hs
  apply re_eq_zero_of_norm_exp_one_cpow
  have h : (χ ⟨Real.exp 1, Real.exp_pos 1⟩ : ℂ) = ((Real.exp 1 : ℝ) : ℂ) ^ s :=
    hs ⟨Real.exp 1, Real.exp_pos 1⟩
  rw [← h, Circle.norm_coe]



theorem existsUnique_addChar_real_units (χ : AddChar ℝ ℂˣ) (hχ : Continuous χ) :
    ∃! s : ℂ, ∀ t : ℝ, (χ t : ℂ) = Complex.exp (s * t) :=
  existsUnique_exp_of_continuous χ hχ χ.map_add_eq_mul

end GroundTheory.Global
