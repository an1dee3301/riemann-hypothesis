module

public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Classical
public import Init.Core
public import Init.Data.Fin.Basic
public import Init.Data.Fin.Lemmas
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Nat.Lemmas
public import Init.Data.NeZero
public import Init.Data.Zero
public import Init.Prelude
public import Init.PropLemmas
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Order.Kleene
public import Mathlib.Algebra.Quotient
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.IsEmpty.Defs
public import Mathlib.Basic.Logic.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Logic.Function.Defs
public import Mathlib.Logic.Pairwise
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Fin.Basic
public import Mathlib.Order.Lattice
public import Mathlib.Order.Notation
public import Mathlib.Order.OrderDual
public import Mathlib.RingTheory.Coprime.Basic
public import Mathlib.RingTheory.Ideal.BigOperators
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Lattice
public import Mathlib.RingTheory.Ideal.Maximal
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.RingTheory.Spectrum.Maximal.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

open MeasureTheory Topology Matrix
open scoped ENNReal NNReal

namespace GlobalTheory.CompanionTheory.SW.SemilocalColumn

private lemma exists_sub_iota_mem_of_sub_involution_mem (A : Type) [CommRing A] [Finite (MaximalSpectrum A)]
    (y : MaximalSpectrum A → A) : ∃ a : A, ∀ M : MaximalSpectrum A, a - y M ∈ M.asIdeal := by
  have hcop : Pairwise (Function.onFun IsCoprime fun M : MaximalSpectrum A => M.asIdeal) := by
    intro M N hMN
    exact Ideal.isCoprime_iff_sup_eq.mpr
      (M.isMaximal.coprime_of_ne N.isMaximal fun h => hMN (MaximalSpectrum.ext h))
  obtain ⟨a, ha⟩ := Ideal.pi_quotient_surjective hcop fun M => Ideal.Quotient.mk M.asIdeal (y M)
  exact ⟨a, fun M => Ideal.Quotient.eq.mp (ha M)⟩

theorem exists_isUnit_add (A : Type) [CommRing A] [Finite (MaximalSpectrum A)] (m : ℕ)
    (x : Fin (m + 1) → A) (hx : ∃ c : Fin (m + 1) → A, ∑ i, c i * x i = 1) :
    ∃ a : Fin m → A, IsUnit (x 0 + ∑ k, a k * x k.succ) := by
  classical
  have hnot : ∀ M : MaximalSpectrum A, x 0 ∈ M.asIdeal → ∃ k : Fin m, x k.succ ∉ M.asIdeal := by
    intro M h0
    by_contra hall
    simp only [not_exists, not_not] at hall
    obtain ⟨c, hc⟩ := hx
    have hmem : ∀ i, x i ∈ M.asIdeal := fun i => Fin.cases h0 hall i
    apply M.isMaximal.ne_top
    rw [Ideal.eq_top_iff_one, ← hc]
    exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (hmem i)
  choose kM hkM using hnot
  let y : Fin m → MaximalSpectrum A → A := fun k M =>
    if h : x 0 ∈ M.asIdeal then (if kM M h = k then 1 else 0) else 0
  choose a ha using fun k => exists_sub_iota_mem_of_sub_involution_mem A (y k)
  refine ⟨a, ?_⟩
  by_contra hu
  obtain ⟨N, hN, hle⟩ := Ideal.exists_le_maximal _ (Ideal.span_singleton_eq_top.not.mpr hu)
  let M : MaximalSpectrum A := ⟨N, hN⟩
  have huM : x 0 + ∑ k, a k * x k.succ ∈ M.asIdeal := hle (Ideal.mem_span_singleton_self _)
  by_cases h0 : x 0 ∈ M.asIdeal
  · have hy : ∑ k, y k M * x k.succ = x (kM M h0).succ := by
      simp only [y, dif_pos h0, ite_mul, one_mul, zero_mul]
      simp [Finset.sum_ite_eq]
    have hin : x 0 + ∑ k, (a k - y k M) * x k.succ ∈ M.asIdeal :=
      M.asIdeal.add_mem h0 (Ideal.sum_mem _ fun k _ => Ideal.mul_mem_right _ _ (ha k M))
    have e : x (kM M h0).succ =
        (x 0 + ∑ k, a k * x k.succ) - (x 0 + ∑ k, (a k - y k M) * x k.succ) := by
      rw [← hy]
      simp only [sub_mul, Finset.sum_sub_distrib]
      ring
    exact hkM M h0 (e ▸ M.asIdeal.sub_mem huM hin)
  · apply h0
    have hs : ∑ k, a k * x k.succ ∈ M.asIdeal := by
      refine Ideal.sum_mem _ fun k _ => Ideal.mul_mem_right _ _ ?_
      simpa [y, h0] using ha k M
    simpa using M.asIdeal.sub_mem huM hs

theorem exists_invertible_first_column :
    ∀ (A : Type) [CommRing A] [Finite (MaximalSpectrum A)] (m : ℕ) (x : Fin (m + 1) → A),
      (∃ c : Fin (m + 1) → A, ∑ i, c i * x i = 1) →
      ∃ g : Matrix (Fin (m + 1)) (Fin (m + 1)) A, IsUnit g.det ∧ ∀ i, g i 0 = x i := by
  intro A _ _ m x hx
  classical
  obtain ⟨a, ha⟩ := exists_isUnit_add A m x hx
  set u := x 0 + ∑ k, a k * x k.succ with hu
  let b : Fin (m + 1) → A := Fin.cons 0 a
  let E : Matrix (Fin (m + 1)) (Fin (m + 1)) A :=
    Matrix.of fun i j => if i = j then 1 else if i = 0 then -b j else 0
  let D : Matrix (Fin (m + 1)) (Fin (m + 1)) A :=
    Matrix.of fun i j => if j = 0 then (if i = 0 then u else x i) else if i = j then 1 else 0
  have hE : E.det = 1 := by
    rw [Matrix.det_of_isUpperTriangular]
    · exact Finset.prod_eq_one fun i _ => by simp [E]
    · intro i j hij
      have hji : j < i := hij
      have hi : i ≠ 0 := by
        rintro rfl
        exact Fin.not_lt_zero _ hji
      simp [E, hji.ne', hi]
  have hD : D.det = u := by
    rw [Matrix.det_of_isLowerTriangular]
    · rw [Fin.prod_univ_succ]
      simp [D, Fin.succ_ne_zero]
    · intro i j hij
      have hij' : i < j := hij
      have hj : j ≠ 0 := by
        rintro rfl
        exact Fin.not_lt_zero _ hij'
      simp [D, hj, hij'.ne]
  refine ⟨E * D, ?_, fun i => ?_⟩
  · rw [Matrix.det_mul, hE, hD, one_mul]
    exact ha
  · rw [Matrix.mul_apply]
    by_cases hi : i = 0
    · subst hi
      rw [Fin.sum_univ_succ]
      simp [E, D, b, (Fin.succ_ne_zero _).symm, hu, Finset.sum_neg_distrib]
    · rw [Finset.sum_eq_single i]
      · simp [E, D, hi]
      · intro j _ hji
        simp [E, D, Ne.symm hji, hi]
      · simp

end GlobalTheory.CompanionTheory.SW.SemilocalColumn
