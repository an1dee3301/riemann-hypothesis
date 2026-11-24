module

public import Mathlib
public import Development.Core20Slim.GroundTheory.GlobalFields.TateThesis.ArchChars
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Positive.Ring
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Field.UnitBall
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.ExistsUnique
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Order.Basic
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.GroupWithZero
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.ContinuousMap.Defs
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Maps.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

namespace GroundTheory.Global

open Complex

theorem ofReal_cpow_eq_exp {r : ℝ} (hr : 0 < r) (u : ℂ) :
    (r : ℂ) ^ u = Complex.exp (u * (Real.log r : ℝ)) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hr.ne'), ← Complex.ofReal_log hr.le,
    mul_comm]

theorem existsUnique_cpow_of_pos (χ : {x : ℝ // 0 < x} →ₜ* ℂˣ) :
    ∃! s : ℂ, ∀ x : {x : ℝ // 0 < x}, (χ x : ℂ) = ((x : ℝ) : ℂ) ^ s := by
  let e : ℝ → {x : ℝ // 0 < x} := fun t => ⟨Real.exp t, Real.exp_pos t⟩
  have econt : Continuous e := Real.continuous_exp.subtype_mk _
  have hlog : ∀ x : {x : ℝ // 0 < x}, e (Real.log x) = x :=
    fun x => Subtype.ext (Real.exp_log x.2)
  obtain ⟨s, hs, -⟩ := existsUnique_exp_of_continuous (fun t => χ (e t))
    (χ.continuous.comp econt)
    (fun a b => by rw [← map_mul]; congr 1; exact Subtype.ext (Real.exp_add a b))
  have hs' : ∀ t : ℝ, (χ (e t) : ℂ) = Complex.exp (s * t) := hs
  refine ⟨s, fun x => ?_, fun s' h' => eq_of_forall_exp_mul_eq fun t => ?_⟩
  · rw [ofReal_cpow_eq_exp x.2, ← hs', hlog]
  · have h1 := h' (e t)
    rw [ofReal_cpow_eq_exp (Real.exp_pos t), Real.log_exp] at h1
    rw [← h1, hs']



noncomputable def circleToUnits : Circle →ₜ* ℂˣ where
  toMonoidHom := Circle.toUnits
  continuous_toFun :=
    Units.isEmbedding_val₀.continuous_iff.mpr (continuous_subtype_val.congr fun _ => rfl)

@[simp] theorem coe_circleToUnits (z : Circle) : ((circleToUnits z : ℂˣ) : ℂ) = z := rfl


end GroundTheory.Global
