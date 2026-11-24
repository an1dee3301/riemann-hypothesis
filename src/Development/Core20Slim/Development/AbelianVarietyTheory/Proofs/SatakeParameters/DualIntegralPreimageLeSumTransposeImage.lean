module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.SatakeParameters.SelfDualOne
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeModelVacuumTranslateClassesIndependent
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmithNormalFormDiscreteValuationFieldStatement
public import Batteries.Logic
public import Formalism.SatakeDualWeyl.StatementF
public import Init.Classical
public import Init.Core
public import Init.Data.Fin.Lemmas
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Opposite
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.WithOne.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.GroupWithZero.Units.Lemmas
public import Mathlib.Algebra.GroupWithZero.WithZero
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Opposite
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Basic
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Opposites
public import Mathlib.Algebra.Order.Group.Int
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.GroupWithZero.WithZero
public import Mathlib.Algebra.Order.IsBotOne
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.TypeTags
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.TypeTags
public import Mathlib.Algebra.Ring.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Opposite
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.IsEmpty.Defs
public import Mathlib.Basic.Logic.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.InvariantBasisNumber
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Lattice
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.Tactic.FieldSimp.Lemmas
public import Mathlib.Topology.Algebra.Valued.ValuationTopology

@[expose] public section

open Matrix

namespace GlobalTheory.LatticeDuality

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem mem_int_iff (a : L) : a ∈ Formalism.UG.intL L ↔ Valued.v a ≤ 1 := Iff.rfl

theorem mulVec_int {m n : ℕ} (A : Matrix (Fin m) (Fin n) L) (u : Fin n → L)
    (hA : ∀ i j, A i j ∈ Formalism.UG.intL L) (hu : ∀ i, u i ∈ Formalism.UG.intL L) :
    ∀ i, (A *ᵥ u) i ∈ Formalism.UG.intL L := fun i => by
  simp only [Matrix.mulVec, dotProduct]
  exact Subring.sum_mem _ fun j _ => Subring.mul_mem _ (hA i j) (hu j)

theorem one_dim (e z : L)
    (h : ∀ c : L, c ∈ Formalism.UG.intL L → e * c ∈ Formalism.UG.intL L → c * z ∈ Formalism.UG.intL L) :
    ∃ a b : L, a ∈ Formalism.UG.intL L ∧ b ∈ Formalism.UG.intL L ∧ z = a + e * b := by
  by_cases he : e ∈ Formalism.UG.intL L
  · refine ⟨z, 0, ?_, Subring.zero_mem _, by simp⟩
    simpa using h 1 (Subring.one_mem _) (by simpa using he)
  · have he0 : e ≠ 0 := by
      rintro rfl
      exact he (Subring.zero_mem _)
    have hlt : 1 < Valued.v e := not_le.mp ((mem_int_iff e).not.mp he)
    have hinv : e⁻¹ ∈ Formalism.UG.intL L := by
      rw [mem_int_iff, map_inv₀]
      exact inv_le_one_of_one_le₀ hlt.le
    refine ⟨0, e⁻¹ * z, Subring.zero_mem _, h _ hinv ?_, ?_⟩
    · rw [mul_inv_cancel₀ he0]; exact Subring.one_mem _
    · field_simp
      simp

theorem diag_case {m n : ℕ} (d : Fin m → L) (z : Fin n → L)
    (h : ∀ u : Fin n → L, (∀ i, u i ∈ Formalism.UG.intL L) →
      (∀ i, ((Matrix.of (fun (j : Fin m) (k : Fin n) => if (k : ℕ) = (j : ℕ) then d j else 0)) *ᵥ u) i
        ∈ Formalism.UG.intL L) → (∑ i, u i * z i) ∈ Formalism.UG.intL L) :
    ∃ l : Fin n → L, ∃ w : Fin m → L, (∀ i, l i ∈ Formalism.UG.intL L) ∧ (∀ i, w i ∈ Formalism.UG.intL L) ∧
      z = l + (Matrix.of (fun (j : Fin m) (k : Fin n) => if (k : ℕ) = (j : ℕ) then d j else 0))ᵀ *ᵥ w := by
  have key : ∀ k : Fin n, ∃ a b : L, a ∈ Formalism.UG.intL L ∧ b ∈ Formalism.UG.intL L ∧
      z k = a + (if hk : (k : ℕ) < m then d ⟨k, hk⟩ else 0) * b := by
    intro k
    apply one_dim
    intro c hc hec
    have := h (Pi.single k c) ?_ ?_
    · simpa [Pi.single_apply] using this
    · intro i
      by_cases hi : i = k
      · subst hi; simpa using hc
      · simp [hi]
    · intro j
      rw [Matrix.mulVec_single]
      by_cases hj : (k : ℕ) = (j : ℕ)
      · have hk : (k : ℕ) < m := hj ▸ j.2
        have : (⟨k, hk⟩ : Fin m) = j := Fin.ext hj
        rw [dite_eq_left hk, this] at hec
        simpa [hj] using hec
      · simp [hj]
  choose a b ha hb hz using key
  refine ⟨a, fun j => if hj : (j : ℕ) < n then b ⟨j, hj⟩ else 0, ha, ?_, ?_⟩
  · intro j
    dsimp only
    split_ifs
    · exact hb _
    · exact Subring.zero_mem _
  · funext k
    rw [hz k, Pi.add_apply]
    congr 1
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.of_apply]
    by_cases hk : (k : ℕ) < m
    · rw [dite_eq_left hk, Finset.sum_eq_single (⟨k, hk⟩ : Fin m)]
      · simp
      · intro j _ hj
        have : (k : ℕ) ≠ (j : ℕ) := fun e => hj (Fin.ext e.symm)
        simp [this]
      · simp
    · rw [dite_eq_right hk, zero_mul]
      symm
      refine Finset.sum_eq_zero fun j _ => ?_
      have : (k : ℕ) ≠ (j : ℕ) := fun e => hk (e ▸ j.2)
      simp [this]

theorem dual_subset : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (m n : ℕ) (x : Matrix (Fin m) (Fin n) L)
    (z : Fin n → L),
    (∀ u : Fin n → L, (∀ i, u i ∈ Formalism.UG.intL L) → (∀ i, (x *ᵥ u) i ∈ Formalism.UG.intL L) → (∑ i, u i * z i) ∈ Formalism.UG.intL L) →
    ∃ l : Fin n → L, ∃ w : Fin m → L, (∀ i, l i ∈ Formalism.UG.intL L) ∧ (∀ i, w i ∈ Formalism.UG.intL L) ∧ z = l + xᵀ *ᵥ w := by
  intro L _ _ m n x z h
  obtain ⟨P, P', Q, Q', d, hP, hP', hQ, hQ', hPP, hQQ, hx⟩ := GlobalTheory.T.smithNormalForm_discreteValuationField L m n x
  set D : Matrix (Fin m) (Fin n) L :=
    Matrix.of (fun (j : Fin m) (k : Fin n) => if (k : ℕ) = (j : ℕ) then d j else 0) with hD
  have hPP' : P' * P = 1 := mul_eq_one_comm.mp hPP
  have hQQ' : Q' * Q = 1 := mul_eq_one_comm.mp hQQ
  obtain ⟨l, w, hl, hw, hz⟩ := diag_case d (Q'ᵀ *ᵥ z) (by
    intro s hs hDs
    have h1 := h (Q' *ᵥ s) (mulVec_int _ _ hQ' hs) (by
      have : x *ᵥ (Q' *ᵥ s) = P *ᵥ (D *ᵥ s) := by
        rw [hx, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc (P * D), hQQ, Matrix.mul_one]
      rw [this]
      exact mulVec_int _ _ hP hDs)
    have h2 : ∑ i, s i * (Q'ᵀ *ᵥ z) i = ∑ i, (Q' *ᵥ s) i * z i := by
      change s ⬝ᵥ (Q'ᵀ *ᵥ z) = (Q' *ᵥ s) ⬝ᵥ z
      rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
    rw [h2]
    exact h1)
  refine ⟨Qᵀ *ᵥ l, P'ᵀ *ᵥ w, mulVec_int _ _ (fun i j => hQ j i) hl,
    mulVec_int _ _ (fun i j => hP' j i) hw, ?_⟩
  have h3 : z = Qᵀ *ᵥ (Q'ᵀ *ᵥ z) := by
    rw [Matrix.mulVec_mulVec, ← Matrix.transpose_mul, hQQ', Matrix.transpose_one, Matrix.one_mulVec]
  have h4 : xᵀ *ᵥ (P'ᵀ *ᵥ w) = Qᵀ *ᵥ (Dᵀ *ᵥ w) := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.transpose_mul, ← Matrix.transpose_mul, hx,
      ← Matrix.mul_assoc, ← Matrix.mul_assoc, hPP', Matrix.one_mul]
  rw [h4, ← Matrix.mulVec_add, ← hz]
  exact h3

end GlobalTheory.LatticeDuality
