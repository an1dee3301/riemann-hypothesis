module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsContOnOfLocal
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdeleJoinZero
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Group.Defs
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Ring.Unbundled.Basic
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Order.ZeroLEOne
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.MulAction
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.IsEmpty.Basic
public import Mathlib.Basic.IsEmpty.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.Real.Star
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.BooleanAlgebra
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Empty
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Finsupp.SMul
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.Logic.Function.Defs
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Lattice
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Positivity.Core
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

open IsDedekindDomain NumberField
open scoped Classical

namespace GlobalTheory

theorem norm_pow_le_const_mul_one_add_sum_abs_coord_pow :
    ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (ι : Type) [Fintype ι] (b : Module.Basis ι ℝ E) (i : ℕ),
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x : E, ‖x‖ ^ i ≤ K * (1 + ∑ c, |b.coord c x| ^ i) := by
  intro E _ _ ι _ b i
  have hB1 : 1 ≤ 1 + ∑ c, ‖b c‖ := by
    have : 0 ≤ ∑ c, ‖b c‖ := Finset.sum_nonneg (fun c _ => norm_nonneg _)
    linarith
  refine ⟨(1 + ∑ c, ‖b c‖) ^ i, by positivity, fun x => ?_⟩
  have hS : 0 ≤ ∑ c, |b.coord c x| ^ i := Finset.sum_nonneg (fun c _ => by positivity)
  have hx : ‖x‖ ≤ ∑ c, |b.coord c x| * ‖b c‖ := by
    conv_lhs => rw [← b.sum_repr x]
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [norm_smul, Real.norm_eq_abs, Module.Basis.coord_apply]
  rcases isEmpty_or_nonempty ι with hι | hι
  · have h0 : ‖x‖ = 0 := by
      have : ∑ c, |b.coord c x| * ‖b c‖ = 0 := by simp
      linarith [norm_nonneg x]
    rw [h0]
    have hp : 1 ≤ (1 + ∑ c, ‖b c‖) ^ i := one_le_pow₀ hB1
    calc (0:ℝ) ^ i ≤ 1 := pow_le_one₀ le_rfl zero_le_one
      _ ≤ (1 + ∑ c, ‖b c‖) ^ i * (1 + ∑ c, |b.coord c x| ^ i) := by nlinarith
  · obtain ⟨c0, -, hc0⟩ := Finset.exists_max_image Finset.univ (fun c => |b.coord c x|)
      Finset.univ_nonempty
    have h1 : ‖x‖ ≤ |b.coord c0 x| * (1 + ∑ c, ‖b c‖) := by
      calc ‖x‖ ≤ ∑ c, |b.coord c x| * ‖b c‖ := hx
        _ ≤ ∑ c, |b.coord c0 x| * ‖b c‖ := Finset.sum_le_sum (fun c _ =>
            mul_le_mul_of_nonneg_right (hc0 c (Finset.mem_univ _)) (norm_nonneg _))
        _ = |b.coord c0 x| * ∑ c, ‖b c‖ := by rw [Finset.mul_sum]
        _ ≤ |b.coord c0 x| * (1 + ∑ c, ‖b c‖) :=
            mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
    have h2 : |b.coord c0 x| ^ i ≤ ∑ c, |b.coord c x| ^ i :=
      Finset.single_le_sum (f := fun c => |b.coord c x| ^ i) (fun c _ => by positivity)
        (Finset.mem_univ c0)
    calc ‖x‖ ^ i ≤ (|b.coord c0 x| * (1 + ∑ c, ‖b c‖)) ^ i :=
          pow_le_pow_left₀ (norm_nonneg _) h1 i
      _ = (1 + ∑ c, ‖b c‖) ^ i * |b.coord c0 x| ^ i := by rw [mul_pow, mul_comm]
      _ ≤ (1 + ∑ c, ‖b c‖) ^ i * (1 + ∑ c, |b.coord c x| ^ i) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          linarith

end GlobalTheory
