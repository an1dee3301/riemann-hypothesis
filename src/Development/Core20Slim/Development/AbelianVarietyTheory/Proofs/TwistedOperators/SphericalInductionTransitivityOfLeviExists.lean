module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryLeviNormalizesUnipotentRadical
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiJMulApply
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.FIwasawa
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.FSatakeA
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.FSatakeC
public import Formalism.SatakeDualWeyl.StatementF
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Fin.Basic
public import Init.Data.Fin.Lemmas
public import Init.Data.Int.Basic
public import Init.Data.Int.Lemmas
public import Init.Data.Int.Order
public import Init.Data.List.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Nat.Lemmas
public import Init.Data.NeZero
public import Init.Data.Order.Lemmas
public import Init.Data.Zero
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
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
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.WithOne.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.GroupWithZero.WithZero
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Order.IsBotOne
public import Mathlib.Algebra.Order.Monoid.Canonical.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Algebra.Order.SuccPred
public import Mathlib.Algebra.Order.ZeroLEOne
public import Mathlib.Algebra.Quotient
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Cast.Order.Basic
public import Mathlib.Data.Nat.Init
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Logic.Function.Defs
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Fin.Basic
public import Mathlib.Order.Lattice
public import Mathlib.Order.Nat
public import Mathlib.Order.RelClasses
public import Mathlib.Order.SuccPred.Nat
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.RingTheory.Valuation.Integers
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Valued.ValuationTopology

@[expose] public section

noncomputable section

open Formalism.UG GlobalTheory.SatakeWeyl

namespace GlobalTheory.InertZeta

section

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {N : ℕ}

theorem blk_mono {i j : Fin (N + 2)} (h : j ≤ i) : blk N j ≤ blk N i := by
  rcases idx_cases i with rfl | ⟨i', rfl⟩ | rfl <;> rcases idx_cases j with rfl | ⟨j', rfl⟩ | rfl <;> simp
  all_goals first
    | (rw [Fin.le_iff_val_le_val] at h; have := i'.2; simp at h; omega)
    | (rw [Fin.le_iff_val_le_val] at h; simp at h; done)
    | (rw [Fin.le_iff_val_le_val] at h; simp at h; omega)

theorem levi_ext {ϖ : L} {a : ℤ} {g₀ : GU σ N} {m m' : GU σ (N + 2)} (h : IsLeviElt ϖ a g₀ m)
    (h' : IsLeviElt ϖ a g₀ m') : m = m' := by
  apply mat_injective
  funext i j
  by_cases hij : blk N i = blk N j
  · rcases idx_cases i with rfl | ⟨i', rfl⟩ | rfl <;> rcases idx_cases j with rfl | ⟨j', rfl⟩ | rfl <;>
      simp at hij
    · rw [h.2.1, h'.2.1]
    · rw [h.2.2.2 i' j', h'.2.2.2 i' j']
    · rw [h.2.2.1, h'.2.2.1]
  · rw [h.1 i j hij, h'.1 i j hij]

theorem levi_mul {ϖ : L} (hϖ : ϖ ≠ 0) {a a' : ℤ} {g g' : GU σ N} {m m' : GU σ (N + 2)} (h : IsLeviElt ϖ a g m)
    (h' : IsLeviElt ϖ a' g' m') : IsLeviElt ϖ (a + a') (g * g') (m * m') := by
  have e : ∀ i j, mat (m * m') i j = mat m i 0 * mat m' 0 j + ∑ l, mat m i (mid l) * mat m' (mid l) j +
      mat m i (Fin.last (N + 1)) * mat m' (Fin.last (N + 1)) j := fun i j => by
    rw [mat_mul, Matrix.mul_apply, sum_idx (fun l => mat m i l * mat m' l j)]
  have z : ∀ i j, blk N i ≠ blk N j → mat m i j = 0 := h.1
  have z' : ∀ i j, blk N i ≠ blk N j → mat m' i j = 0 := h'.1
  refine ⟨mul_mem h.1 h'.1, ?_, ?_, fun i j => ?_⟩
  · rw [e, h.2.1, h'.2.1, z 0 (Fin.last (N + 1)) (by simp), zero_mul, add_zero,
      Finset.sum_eq_zero (fun l _ => by rw [z 0 (mid l) (by simp), zero_mul]), add_zero, zpow_add₀ hϖ]
  · rw [e, h.2.2.1, h'.2.2.1, z (Fin.last (N + 1)) 0 (by simp), zero_mul, zero_add,
      Finset.sum_eq_zero (fun l _ => by rw [z (Fin.last (N + 1)) (mid l) (by simp), zero_mul]), zero_add,
      neg_add, zpow_add₀ hϖ]
  · rw [e, z (mid i) 0 (by simp), z (mid i) (Fin.last (N + 1)) (by simp), zero_mul, zero_mul, zero_add, add_zero,
      mat_mul, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [h.2.2.2, h'.2.2.2]

end

theorem sphTrans (hL : LeviExists) : SphTrans := by
  intro L _ _ ϖ σ q N r hU hr α φ φ₀ hα hsph h1 hsph₀ h10 a g₀ m hm u hu
  have hϖ : ϖ ≠ 0 := by
    intro h; have := hU.2.2.2.1; rw [h, Valuation.map_zero] at this; exact WithZero.zero_ne_coe this
  obtain ⟨b₀, k₀, hb₀, hk₀, rfl⟩ := P.fIwasawa_iwasawa σ hU.1 hU.2.1 g₀
  obtain ⟨mb, hmb⟩ := hL L ϖ σ q N hU a b₀
  obtain ⟨mk, hmk⟩ := hL L ϖ σ q N hU 0 k₀
  have hm' : m = mb * mk := by
    have := levi_mul hϖ hmb hmk
    rw [add_zero] at this
    exact levi_ext hm this
  subst hm'

  have hmkK : mk ∈ KU σ (N + 2) := by
    rw [mem_KU_iff hU.2.1]
    intro i j
    by_cases hij : blk N i = blk N j
    · rcases idx_cases i with rfl | ⟨i', rfl⟩ | rfl <;> rcases idx_cases j with rfl | ⟨j', rfl⟩ | rfl <;>
        simp at hij
      · rw [hmk.2.1, zpow_zero]; exact one_mem _
      · rw [hmk.2.2.2 i' j']; exact P.fSatake_K_int hk₀ i' j'
      · rw [hmk.2.2.1, neg_zero, zpow_zero]; exact one_mem _
    · rw [hmk.1 i j hij]; exact zero_mem _
  set v := mk * u * mk⁻¹ with hv
  have hvR : v ∈ radQ σ N := (leviRad L σ (N + 2) (blk N) hU.2.1 mk hmk.1 u hu).1
  have hdiag : ∀ i j, blk N j ≤ blk N i → mat (mb * v) i j = mat mb i j :=
    fun i j h => levi_mul_rad_apply hmb.1 hvR h
  have hB : IsBorelU (mb * v) := by
    intro i j hji
    show mat (mb * v) i j = 0
    rw [hdiag i j (blk_mono hji.le)]
    by_cases hij : blk N i = blk N j
    · rcases idx_cases i with rfl | ⟨i', rfl⟩ | rfl <;> rcases idx_cases j with rfl | ⟨j', rfl⟩ | rfl <;>
        simp at hij
      · exact absurd hji (lt_irrefl _)
      · rw [hmb.2.2.2 i' j']
        exact hb₀ i' j' (by rw [Fin.lt_iff_val_lt_val] at hji ⊢; simpa using hji)
      · exact absurd hji (lt_irrefl _)
    · exact hmb.1 i j hij
  have e1 : mb * mk * u = (mb * v) * 1 * mk := by rw [hv]; group
  have hφ : φ (mb * mk * u) = chiDeltaU q α (mb * v) := by
    rw [e1, hsph _ _ _ hB hmkK, h1, mul_one]
  have hφ₀ : φ₀ (b₀ * k₀) = chiDeltaU q (Fin.tail α) b₀ := by
    have := hsph₀ b₀ 1 k₀ hb₀ hk₀
    rwa [mul_one, h10, mul_one] at this
  rw [hφ, hφ₀]
  unfold chiDeltaU
  rw [Fin.prod_univ_succ]
  congr 1
  · rw [dite_eq_left (by simp)]
    have e0 : (⟨(0 : Fin (r + 1)).val, by simp⟩ : Fin (N + 2)) = 0 := rfl
    rw [e0]
    show α 0 ^ ordL (mat (mb * v) 0 0) * (q : ℂ) ^ (-ordL (mat (mb * v) 0 0) * (((N + 2 : ℕ) : ℤ) - 1 - 2 * ((0 : ℕ) : ℤ))) = _
    rw [hdiag 0 0 le_rfl, hmb.2.1, P.fSatake_ord_zpow hU.2.2.2.1]
    congr 2
    push_cast
    ring
  · refine Finset.prod_congr rfl fun i _ => ?_
    have hiN : i.val < N := by have := i.2; omega
    rw [dite_eq_left (by simp; omega), dite_eq_left hiN]
    have ei : (⟨(Fin.succ i).val, by simp; omega⟩ : Fin (N + 2)) = mid ⟨i.val, hiN⟩ := by
      ext; simp
    rw [ei]
    show α i.succ ^ ordL (mat (mb * v) (mid ⟨i.val, hiN⟩) (mid ⟨i.val, hiN⟩)) *
      (q : ℂ) ^ (-ordL (mat (mb * v) (mid ⟨i.val, hiN⟩) (mid ⟨i.val, hiN⟩)) *
        (((N + 2 : ℕ) : ℤ) - 1 - 2 * ((i.succ.val : ℕ) : ℤ))) = _
    rw [hdiag _ _ le_rfl, hmb.2.2.2]
    show _ = Fin.tail α i ^ ordL (mat b₀ ⟨i.val, hiN⟩ ⟨i.val, hiN⟩) *
      (q : ℂ) ^ (-ordL (mat b₀ ⟨i.val, hiN⟩ ⟨i.val, hiN⟩) * ((N : ℤ) - 1 - 2 * ((i.val : ℕ) : ℤ)))
    congr 2
    simp only [Fin.val_succ]
    push_cast
    ring

end GlobalTheory.InertZeta

end
