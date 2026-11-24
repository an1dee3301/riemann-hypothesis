module

public import Mathlib
public import Init.Classical
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Fin.Basic
public import Init.Data.Function
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.NeZero
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.Group.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.ExistsOfLE
public import Mathlib.Algebra.Order.Ring.Basic
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Ring.Unbundled.Basic
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.Analysis.PSeries
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.IsEmpty.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.Real.Star
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Basic.Unique
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Int.Cast.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Int.Cast.Lemmas
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Cast.Order.Basic
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Insert
public import Mathlib.Data.Set.Operations
public import Mathlib.Data.Subtype
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Logic.Function.Defs
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.Cofinite
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Lattice
public import Mathlib.Order.Notation
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Positivity.Core
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.Group
public import Mathlib.Topology.Algebra.InfiniteSum.Ring
public import Mathlib.Topology.Algebra.InfiniteSum.SummationFilter
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs
public import Mathlib.Topology.UniformSpace.Real

@[expose] public section

open MeasureTheory

namespace GlobalTheory.CompanionTheory.LatticeCount

theorem summable_inv_one_add_sq_int :
    Summable (fun m : ℤ => ((1 : ℝ) + (m : ℝ) ^ 2)⁻¹) := by
  have h : Summable (fun m : ℤ => 1 / (m : ℝ) ^ 2) :=
    (Real.summable_one_div_int_pow (p := 2)).2 (by norm_num)
  refine Summable.of_norm_bounded_eventually h ?_
  have hfin : ({0} : Set ℤ).Finite := Set.finite_singleton 0
  refine Filter.mem_cofinite.2 (hfin.subset ?_)
  intro m hm
  by_contra h0
  have h0' : m ≠ 0 := by simpa using h0
  apply hm
  have hm0 : (0 : ℝ) < (m : ℝ) ^ 2 := by
    have : (m : ℝ) ≠ 0 := by exact_mod_cast h0'
    positivity
  have hpos : (0 : ℝ) < 1 + (m : ℝ) ^ 2 := by positivity
  show ‖((1 : ℝ) + (m : ℝ) ^ 2)⁻¹‖ ≤ 1 / (m : ℝ) ^ 2
  rw [Real.norm_of_nonneg (inv_nonneg.2 hpos.le), one_div]
  exact inv_anti₀ hm0 (by linarith)

theorem summable_prod_inv_one_add_sq (d : ℕ) :
    Summable (fun n : Fin d → ℤ => ∏ k, ((1 : ℝ) + (n k : ℝ) ^ 2)⁻¹) := by
  induction d with
  | zero => exact Summable.of_finite
  | succ d ih =>
    have h2 := summable_inv_one_add_sq_int.mul_of_nonneg ih
      (fun m => by positivity) (fun n => Finset.prod_nonneg (fun k _ => by positivity))
    rw [← (Fin.consEquiv (fun _ : Fin (d + 1) => ℤ)).summable_iff]
    refine h2.congr ?_
    intro x
    simp [Fin.prod_univ_succ, Fin.consEquiv]
    exact mul_comm _ _

theorem summable_of_lattice_decay (ι : Type) (d : ℕ) (w : ι → ℂ) (f : ι → Fin d → ℝ)
    (hf : Function.Injective f) (N : ℕ) (hN : 0 < N) (C : ℝ)
    (hC : ∀ i, ‖w i‖ * ∏ k, (1 + f i k ^ 2) ≤ C)
    (hint : ∀ i, w i ≠ 0 → ∀ k, ∃ n : ℤ, (N : ℝ) * f i k = n) : Summable w := by
  classical
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  let S := {i // w i ≠ 0}
  choose n hn using fun i : S => hint i.1 i.2
  have hinj : Function.Injective n := by
    intro a b hab
    apply Subtype.ext
    apply hf
    funext k
    have h1 := hn a k
    have h2 := hn b k
    rw [hab] at h1
    exact mul_left_cancel₀ hNpos.ne' (h1.trans h2.symm)
  have hg := ((summable_prod_inv_one_add_sq d).comp_injective hinj).mul_left (((N : ℝ) ^ 2) ^ d * C)
  have hbound : ∀ a : S, ‖w a.1‖ ≤ ((N : ℝ) ^ 2) ^ d * C *
      ∏ k, ((1 : ℝ) + (n a k : ℝ) ^ 2)⁻¹ := by
    intro a
    have hle : ∏ k, ((1 : ℝ) + (n a k : ℝ) ^ 2) ≤
        ((N : ℝ) ^ 2) ^ d * ∏ k, (1 + f a.1 k ^ 2) := by
      have : ((N : ℝ) ^ 2) ^ d * ∏ k, (1 + f a.1 k ^ 2) =
          ∏ k : Fin d, ((N : ℝ) ^ 2 * (1 + f a.1 k ^ 2)) := by
        rw [Finset.prod_mul_distrib]; simp
      rw [this]
      refine Finset.prod_le_prod₀ (fun k _ => by positivity) (fun k _ => ?_)
      rw [← hn a k]
      have : (1 : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
      nlinarith
    have hpos : (0 : ℝ) < ∏ k, ((1 : ℝ) + (n a k : ℝ) ^ 2) :=
      Finset.prod_pos (fun k _ => by positivity)
    rw [Finset.prod_inv_distrib, ← div_eq_mul_inv, le_div_iff₀ hpos]
    calc ‖w a.1‖ * ∏ k, ((1 : ℝ) + (n a k : ℝ) ^ 2)
        ≤ ‖w a.1‖ * (((N : ℝ) ^ 2) ^ d * ∏ k, (1 + f a.1 k ^ 2)) :=
          mul_le_mul_of_nonneg_left hle (norm_nonneg _)
      _ = ((N : ℝ) ^ 2) ^ d * (‖w a.1‖ * ∏ k, (1 + f a.1 k ^ 2)) := by ring
      _ ≤ ((N : ℝ) ^ 2) ^ d * C := mul_le_mul_of_nonneg_left (hC _) (by positivity)
  have hsub : Summable (w ∘ (Subtype.val : S → ι)) :=
    Summable.of_norm_bounded hg hbound
  refine (Function.Injective.summable_iff Subtype.val_injective ?_).1 hsub
  intro x hx
  by_contra h0
  exact hx ⟨⟨x, h0⟩, rfl⟩

end GlobalTheory.CompanionTheory.LatticeCount
