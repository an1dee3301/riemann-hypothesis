module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormIteratedFDerivRemCompLe
public import Batteries.Logic
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Order.Lemmas
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.IsApply
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Hom.Basic
public import Mathlib.Algebra.Order.Hom.GroupNorm
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Monoid.Unbundled.ExistsOfLE
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Algebra.Order.Ring.Basic
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Ring.Unbundled.Basic
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.Distribution.TemperateGrowth
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Module.Seminorm.Basic
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Logic.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.Real.Star
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Cast.Order.Ring
public import Mathlib.Data.Nat.Init
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Order.Lattice
public import Mathlib.Order.Nat
public import Mathlib.Order.RelClasses
public import Mathlib.Tactic.FieldSimp.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Positivity.Core
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Instances.RealVectorSpace
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Metrizable.Basic
public import Mathlib.Topology.Metrizable.Uniformity
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open scoped SchwartzMap

namespace GlobalTheory.LinearPhase

open Complex GlobalTheory.CharFormDeriv

theorem seminorm_phase_sub_le : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (L : V →L[ℝ] ℝ) (c : ℝ) (f : 𝓢(V, ℂ)) (k n : ℕ), ∃ C : ℝ, ∀ t : ℝ, |t| ≤ 1 → SchwartzMap.seminorm ℂ k n (SchwartzMap.smulLeftCLM ℂ (fun x => Complex.exp (-(2 * Real.pi * Complex.I) * ((t * L x + t ^ 2 * c : ℝ) : ℂ))) f - f + ((t : ℂ) * (2 * Real.pi * Complex.I)) • SchwartzMap.smulLeftCLM ℂ (fun x => ((L x : ℝ) : ℂ)) f) ≤ C * t ^ 2 := by
  intro V _ _ L c f k n
  set L' : V →L[ℝ] ℝ := (-(2 * Real.pi)) • L with hL'
  have hL'x : ∀ x, ((L' x : ℝ) : ℂ) = -(2 * Real.pi) * (L x : ℂ) := fun x => by
    simp [hL']
  set K := 3 * 2 ^ n * (1 + ‖L'‖) ^ (n + 2) *
      (2 ^ (k + 2) * ((Finset.Iic (k + 2, n)).sup fun m => SchwartzMap.seminorm ℂ m.1 m.2) f)
      with hK
  have hgt : Function.HasTemperateGrowth (fun x : V => ((L x : ℝ) : ℂ)) :=
    (Complex.ofRealCLM.comp L).hasTemperateGrowth
  set g : 𝓢(V, ℂ) := SchwartzMap.smulLeftCLM ℂ (fun x => ((L x : ℝ) : ℂ)) f with hgdef
  have hg : ∀ x, g x = (L x : ℂ) * f x := fun x => by
    rw [hgdef, SchwartzMap.smulLeftCLM_apply_apply hgt, smul_eq_mul]
  refine ⟨K + 2 * |2 * Real.pi * c| *
    (SchwartzMap.seminorm ℂ k n f + 2 * Real.pi * SchwartzMap.seminorm ℂ k n g), fun t ht1 => ?_⟩
  set a : ℂ := Complex.exp (((-(2 * Real.pi * c * t ^ 2) : ℝ) : ℂ) * I) with ha
  have hfun : (fun x : V => Complex.exp (-(2 * Real.pi * Complex.I) * ((t * L x + t ^ 2 * c : ℝ) : ℂ)))
      = fun x : V => a * Complex.exp ((I * t) * (L' x : ℂ)) := by
    funext x
    rw [ha, ← Complex.exp_add, hL'x]
    congr 1
    push_cast
    ring
  have het : Function.HasTemperateGrowth fun x : V => a * Complex.exp ((I * t) * (L' x : ℂ)) :=
    (Function.HasTemperateGrowth.const a).mul (hasTemperateGrowth_char L' t)
  rw [hfun]
  set A : 𝓢(V, ℂ) := SchwartzMap.smulLeftCLM ℂ
    (fun x : V => Complex.exp ((I * t) * (L' x : ℂ))) f with hAdef
  have hA : ∀ x, A x = Complex.exp ((I * t) * (L' x : ℂ)) * f x := fun x => by
    rw [hAdef, SchwartzMap.smulLeftCLM_apply_apply (hasTemperateGrowth_char L' t), smul_eq_mul]
  set E : 𝓢(V, ℂ) := SchwartzMap.smulLeftCLM ℂ
    (fun x : V => a * Complex.exp ((I * t) * (L' x : ℂ))) f with hEdef
  have hE : ∀ x, E x = a * Complex.exp ((I * t) * (L' x : ℂ)) * f x := fun x => by
    rw [hEdef, SchwartzMap.smulLeftCLM_apply_apply het, smul_eq_mul]
  rcases eq_or_ne t 0 with ht0 | ht0
  · have h0 : E - f + ((t : ℂ) * (2 * Real.pi * Complex.I)) • g = 0 := by
      ext x
      simp only [SchwartzMap.add_apply, SchwartzMap.sub_apply, SchwartzMap.smul_apply, hE, ha, ht0]
      simp
    rw [h0, map_zero, ht0]
    simp
  have ht : (t : ℂ) ≠ 0 := by exact_mod_cast ht0
  set u : 𝓢(V, ℂ) := (t : ℂ)⁻¹ • (A - f) + (2 * Real.pi * I : ℂ) • g with hudef
  have hu : ∀ x, u x = rem t (L' x) * f x := fun x => by
    simp only [hudef, SchwartzMap.add_apply, SchwartzMap.sub_apply, SchwartzMap.smul_apply, hA, hg,
      rem, smul_eq_mul, hL'x]
    ring
  have hub : SchwartzMap.seminorm ℂ k n u ≤ |t| * K := seminorm_rem_mul_le L' f u ht0 ht1 hu k n
  have hid : E - f + ((t : ℂ) * (2 * Real.pi * Complex.I)) • g
      = (a * t) • u + ((a - 1) • f + (-((a - 1) * t * (2 * Real.pi * I))) • g) := by
    ext x
    simp only [hudef, SchwartzMap.add_apply, SchwartzMap.sub_apply, SchwartzMap.smul_apply, hA, hE,
      smul_eq_mul]
    field_simp
    ring
  have hna : ‖a‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  have hna1 : ‖a - 1‖ ≤ 2 * |2 * Real.pi * c| * t ^ 2 := by
    refine (norm_cexp_mul_I_sub_one_le _).trans (le_of_eq ?_)
    rw [abs_neg, abs_mul (2 * Real.pi * c), abs_of_nonneg (sq_nonneg t)]
    ring
  have hpf := apply_nonneg (SchwartzMap.seminorm ℂ k n) f
  have hpg := apply_nonneg (SchwartzMap.seminorm ℂ k n) g
  have hpi := Real.pi_pos
  have hn1 : ‖a * t‖ = |t| := by rw [norm_mul, hna, one_mul, Complex.norm_real, Real.norm_eq_abs]
  have hn2 : ‖-((a - 1) * t * (2 * Real.pi * I))‖ ≤ 2 * |2 * Real.pi * c| * t ^ 2 * (2 * Real.pi) := by
    have h2 : ‖(2 * Real.pi * I : ℂ)‖ = 2 * Real.pi := by
      simp [abs_of_pos hpi]
    rw [norm_neg, norm_mul, norm_mul, h2, Complex.norm_real, Real.norm_eq_abs]
    calc ‖a - 1‖ * |t| * (2 * Real.pi) ≤ (2 * |2 * Real.pi * c| * t ^ 2) * 1 * (2 * Real.pi) := by
          gcongr
      _ = _ := by ring
  rw [hid]
  calc SchwartzMap.seminorm ℂ k n ((a * t) • u + ((a - 1) • f + (-((a - 1) * t * (2 * Real.pi * I))) • g))
      ≤ SchwartzMap.seminorm ℂ k n ((a * t) • u) + (SchwartzMap.seminorm ℂ k n ((a - 1) • f) +
          SchwartzMap.seminorm ℂ k n ((-((a - 1) * t * (2 * Real.pi * I))) • g)) :=
        (map_add_le_add _ _ _).trans (by gcongr; exact map_add_le_add _ _ _)
    _ = |t| * SchwartzMap.seminorm ℂ k n u + (‖a - 1‖ * SchwartzMap.seminorm ℂ k n f +
          ‖-((a - 1) * t * (2 * Real.pi * I))‖ * SchwartzMap.seminorm ℂ k n g) := by
        rw [map_smul_eq_mul, map_smul_eq_mul, map_smul_eq_mul, hn1]
    _ ≤ |t| * (|t| * K) + (2 * |2 * Real.pi * c| * t ^ 2 * SchwartzMap.seminorm ℂ k n f +
          2 * |2 * Real.pi * c| * t ^ 2 * (2 * Real.pi) * SchwartzMap.seminorm ℂ k n g) := by
        gcongr
    _ = _ := by
        rw [← mul_assoc, ← sq, sq_abs]; ring

end GlobalTheory.LinearPhase
