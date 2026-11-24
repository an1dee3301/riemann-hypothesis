module

public import Mathlib
public import Init.Core
public import Init.Data.Fin.Basic
public import Init.Data.Nat.Basic
public import Init.Data.NeZero
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.IsEmpty.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Basic.Unique
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Finset.BooleanAlgebra
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Empty
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Order.Defs.Prop
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.Group
public import Mathlib.Topology.Algebra.InfiniteSum.Ring
public import Mathlib.Topology.Algebra.InfiniteSum.SummationFilter
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.GDelta.MetrizableSpace
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Metrizable.Basic
public import Mathlib.Topology.Metrizable.Uniformity
public import Mathlib.Topology.Separation.CompletelyRegular
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

namespace ReciprocityTheory.ThetaSummability.Est

open Module

theorem summable_and_tsum_pi_prod {α : Type*} {q : ℕ} (f : Fin q → α → ℝ)
    (hf0 : ∀ i a, 0 ≤ f i a) (hf : ∀ i, Summable (f i)) :
    Summable (fun x : Fin q → α => ∏ i, f i (x i)) ∧
      ∑' x : Fin q → α, ∏ i, f i (x i) = ∏ i, ∑' a, f i a := by
  induction q with
  | zero =>
    simp only [Finset.univ_eq_empty, Finset.prod_empty]
    exact ⟨Summable.of_finite, by rw [tsum_const, Nat.card_unique, one_smul]⟩
  | succ q ih =>
    obtain ⟨hs, ht⟩ := ih (fun i => f i.succ) (fun i => hf0 i.succ) (fun i => hf i.succ)
    obtain ⟨e, he⟩ : ∃ e : α × (Fin q → α) ≃ (Fin (q + 1) → α),
        ∀ p, e p = (Fin.cons p.1 p.2 : Fin (q + 1) → α) :=
      ⟨Fin.consEquiv (fun _ : Fin (q + 1) => α), fun p => rfl⟩
    have key : ∀ p : α × (Fin q → α), ∏ i, f i (e p i) = f 0 p.1 * ∏ i, f i.succ (p.2 i) := by
      intro p
      rw [he, Fin.prod_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
    have hprod : Summable (fun p : α × (Fin q → α) => f 0 p.1 * ∏ i, f i.succ (p.2 i)) := by
      have h1 : (0 : α → ℝ) ≤ f 0 := Pi.le_def.mpr fun a => hf0 0 a
      have h2 : (0 : (Fin q → α) → ℝ) ≤ fun x => ∏ i, f i.succ (x i) :=
        Pi.le_def.mpr fun x => Finset.prod_nonneg fun i _ => hf0 _ _
      have hs0 : Summable (fun x : Fin q → α => ∏ i, f i.succ (x i)) := hs
      have hf00 : Summable (f 0) := hf 0
      have := Summable.mul_of_nonneg hf00 hs0 h1 h2
      exact this
    have hs' : Summable (fun p : α × (Fin q → α) => ∏ i, f i (e p i)) :=
      hprod.congr fun p => (key p).symm
    refine ⟨(e.summable_iff (f := fun x : Fin (q + 1) → α => ∏ i, f i (x i))).mp hs', ?_⟩
    calc ∑' x : Fin (q + 1) → α, ∏ i, f i (x i)
        = ∑' p : α × (Fin q → α), ∏ i, f i (e p i) := (e.tsum_eq (fun x => ∏ i, f i (x i))).symm
      _ = ∑' p : α × (Fin q → α), f 0 p.1 * ∏ i, f i.succ (p.2 i) := tsum_congr key
      _ = (∑' a, f 0 a) * ∑' x : Fin q → α, ∏ i, f i.succ (x i) := (Summable.tsum_mul_tsum (hf 0) hs hprod).symm
      _ = ∏ i, ∑' a, f i a := by rw [ht, Fin.prod_univ_succ]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]

end ReciprocityTheory.ThetaSummability.Est
