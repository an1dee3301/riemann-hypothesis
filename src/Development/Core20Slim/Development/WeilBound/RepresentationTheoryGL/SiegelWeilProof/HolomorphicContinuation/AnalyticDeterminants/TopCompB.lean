module

public import Mathlib
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Fin.Basic
public import Init.Data.Fin.Lemmas
public import Init.Data.Function
public import Init.Data.Int.Basic
public import Init.Data.Int.Lemmas
public import Init.Data.Int.Order
public import Init.Data.List.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Nat.Lemmas
public import Init.Data.NeZero
public import Init.Data.Zero
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Prelude
public import Init.PropLemmas
public import Init.SimpLemmas
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.Group.Defs
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.IsEmpty.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Cast.Order.Basic
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Operations
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Order.Lattice
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.CancelDenoms.Core
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.Linarith.Preprocessing
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Positivity.Core
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Module.Multilinear.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

open Polynomial

namespace PositivityTheory.Rg.Sw.LVs.TC

theorem ml_expand {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] {k : ℕ}
    (A : ContinuousMultilinearMap ℂ (fun _ : Fin k => V) ℂ) (Y : Fin k → Fin 3 → V) (z : ℂ) :
    A (fun i => Y i 0 + z • Y i 1 + z ^ 2 • Y i 2) =
      ∑ f : Fin k → Fin 3, z ^ (∑ i, (f i : ℕ)) * A (fun i => Y i (f i)) := by
  have h : (fun i => Y i 0 + z • Y i 1 + z ^ 2 • Y i 2) = fun i => ∑ w : Fin 3, z ^ (w : ℕ) • Y i w := by
    funext i; simp [Fin.sum_univ_three]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [h, ContinuousMultilinearMap.map_sum]
  refine Finset.sum_congr (by simp) fun f _ => ?_
  rw [ContinuousMultilinearMap.map_smul_univ, Finset.prod_pow_eq_pow_sum, smul_eq_mul]

theorem sum_eq_top {k : ℕ} (f : Fin k → Fin 3) (h : ∑ i, (f i : ℕ) = 2 * k) : ∀ i, f i = 2 := by
  by_contra hne
  push Not at hne
  obtain ⟨i, hi⟩ := hne
  have hle : ∀ x, (f x : ℕ) ≤ 2 := fun x => by omega
  have hlt : (f i : ℕ) < 2 := by
    rcases Nat.lt_or_ge (f i : ℕ) 2 with h' | h'
    · exact h'
    · exact absurd (Fin.ext (by simp; omega)) hi
  have : ∑ x, (f x : ℕ) < ∑ _x : Fin k, 2 :=
    Finset.sum_lt_sum (fun x _ => hle x) ⟨i, Finset.mem_univ _, hlt⟩
  simp at this
  omega

theorem infinite_circle : Set.Infinite (Set.range fun θ : ℝ => Complex.exp (2 * θ * Complex.I)) := by
  have hinj : Function.Injective fun m : ℕ => Complex.exp (2 * ((1 : ℝ) / (m + 2) : ℝ) * Complex.I) := by
    intro a b hab
    have hre := congrArg Complex.re hab
    simp only at hre
    have e1 : ∀ x : ℝ, (Complex.exp (2 * (x : ℂ) * Complex.I)).re = Real.cos (2 * x) := by
      intro x
      rw [show 2 * (x : ℂ) * Complex.I = ((2 * x : ℝ) : ℂ) * Complex.I by push_cast; ring, Complex.exp_ofReal_mul_I_re]
    rw [e1, e1] at hre
    have ha : 2 * ((1 : ℝ) / (a + 2)) ∈ Set.Icc 0 Real.pi := by
      constructor
      · positivity
      · have : (2 : ℝ) * (1 / (a + 2)) ≤ 1 := by
          rw [mul_one_div, div_le_one (by positivity)]; linarith [(Nat.cast_nonneg a : (0 : ℝ) ≤ a)]
        linarith [Real.pi_gt_three]
    have hb : 2 * ((1 : ℝ) / (b + 2)) ∈ Set.Icc 0 Real.pi := by
      constructor
      · positivity
      · have : (2 : ℝ) * (1 / (b + 2)) ≤ 1 := by
          rw [mul_one_div, div_le_one (by positivity)]; linarith [(Nat.cast_nonneg b : (0 : ℝ) ≤ b)]
        linarith [Real.pi_gt_three]
    have := Real.injOn_cos ha hb hre
    have h2 : (1 : ℝ) / (a + 2) = 1 / (b + 2) := by linarith
    rw [div_eq_div_iff (by positivity) (by positivity)] at h2
    exact_mod_cast (by linarith : (a : ℝ) = b)
  refine Set.infinite_of_injective_forall_mem hinj fun m => ⟨_, rfl⟩

theorem top_vanish {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] {k : ℕ} {ι : Type*} [Fintype ι]
    (A : ContinuousMultilinearMap ℂ (fun _ : Fin k => V) ℂ) (sg : ι → ℂ) (Y : ι → Fin k → Fin 3 → V)
    (h : ∀ θ : ℝ, ∑ σ, sg σ * A (fun i => Y σ i 0 + Complex.exp (2 * θ * Complex.I) • Y σ i 1 +
      Complex.exp (2 * θ * Complex.I) ^ 2 • Y σ i 2) = 0) :
    ∑ σ, sg σ * A (fun i => Y σ i 2) = 0 := by
  set Q : ℂ[X] := ∑ σ, C (sg σ) * ∑ f : Fin k → Fin 3, C (A (fun i => Y σ i (f i))) * X ^ (∑ i, (f i : ℕ)) with hQ
  have heval : ∀ z : ℂ, Q.eval z = ∑ σ, sg σ * A (fun i => Y σ i 0 + z • Y σ i 1 + z ^ 2 • Y σ i 2) := by
    intro z
    simp only [hQ, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [ml_expand]
    congr 1
    refine Finset.sum_congr rfl fun f _ => ?_
    ring
  have hQ0 : Q = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    refine Set.Infinite.mono ?_ infinite_circle
    rintro _ ⟨θ, rfl⟩
    simp only [Set.mem_ofPred_eq, IsRoot.def, heval, h θ]
  have hc := congrArg (fun p : ℂ[X] => p.coeff (2 * k)) hQ0
  simp only [hQ, finsetSum_coeff, coeff_C_mul, coeff_X_pow, coeff_zero] at hc
  rw [← hc]
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 1
  rw [Finset.sum_eq_single (fun _ => 2)]
  · simp only [Fin.isValue, Fin.val_two, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    rw [if_pos (by ring), mul_one]
  · intro f _ hf
    rw [if_neg, mul_zero]
    intro h2
    exact hf (funext (sum_eq_top f h2.symm))
  · simp

end PositivityTheory.Rg.Sw.LVs.TC
