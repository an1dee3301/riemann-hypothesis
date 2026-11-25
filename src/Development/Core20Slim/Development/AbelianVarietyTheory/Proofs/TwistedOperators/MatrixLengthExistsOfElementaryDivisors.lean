module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen
public import Formalism.SatakeDualWeyl.StatementF
public import Init.ByCases
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Int.Lemmas
public import Init.Data.Int.LemmasAux
public import Init.Data.Int.Order
public import Init.Data.Zero
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Omega.Logic
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.WithOne.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.WithZero
public import Mathlib.Algebra.Order.Group.Int
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.TypeTags
public import Mathlib.Algebra.Order.Monoid.Unbundled.Pow
public import Mathlib.Algebra.Order.Monoid.Unbundled.TypeTags
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Int
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Topology.Algebra.Valued.ValuationTopology

@[expose] public section

open GlobalTheory.InertZeta

noncomputable section
open Matrix Formalism.UG

namespace GlobalTheory.InertZeta

theorem prod_exp_eq {ι : Type} (s : Finset ι) (f : ι → ℤ) :
    ∏ i ∈ s, WithZero.exp (f i) = WithZero.exp (∑ i ∈ s, f i) := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih => rw [Finset.prod_cons, Finset.sum_cons, ih, WithZero.exp_add]

theorem isInt_diagonal {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ} {f : Fin n → L}
    (hf : ∀ i, f i ∈ intL L) : IsInt (Matrix.diagonal f) := fun i j => by
  rw [Matrix.diagonal_apply]
  split_ifs with h
  · subst h; exact hf i
  · exact zero_mem _

theorem hasLen_diagonal_zpow {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ} {ϖ : L}
    (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) (d : Fin n → ℤ) :
    HasLen (Matrix.diagonal (fun i => ϖ ^ d i)) (∑ i, (-d i).toNat) := by
  have h0 : ϖ ≠ 0 := fun h => by rw [h, map_zero] at hϖ; exact WithZero.exp_ne_zero hϖ.symm
  have hpow : ∀ m : ℕ, ϖ ^ m ∈ intL L := fun m => by
    show Valued.v (ϖ ^ m) ≤ 1
    rw [map_pow, hϖ]
    exact pow_le_one' (by rw [← WithZero.exp_zero, WithZero.exp_le_exp]; norm_num) m
  refine ⟨Matrix.diagonal (fun i => if 0 ≤ d i then 1 else 0), Matrix.diagonal (fun i => if 0 ≤ d i then 0 else 1),
    Matrix.diagonal (fun i => ϖ ^ (-d i).toNat), ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · exact isInt_diagonal fun i => by split_ifs <;> first | exact one_mem _ | exact zero_mem _
  · exact isInt_diagonal fun i => by split_ifs <;> first | exact one_mem _ | exact zero_mem _
  · exact isInt_diagonal fun i => hpow _
  · rw [Matrix.diagonal_mul_diagonal]
    refine isInt_diagonal fun i => ?_
    have : ϖ ^ d i * ϖ ^ (-d i).toNat = ϖ ^ (d i).toNat := by
      rw [← zpow_natCast, ← zpow_add₀ h0, ← zpow_natCast]
      congr 1
      omega
    rw [this]; exact hpow _
  · rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_add, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    by_cases h : 0 ≤ d i
    · simp [h, Int.toNat_eq_zero.2 (by omega : -d i ≤ 0)]
    · simp only [h, if_false, zero_mul, zero_add, one_mul]
      rw [← zpow_natCast, ← zpow_add₀ h0]
      rw [show d i + (((-d i).toNat : ℕ) : ℤ) = 0 by omega, zpow_zero]
  · rw [Matrix.det_diagonal, map_prod]
    simp only [map_pow, hϖ]
    rw [Finset.prod_congr rfl (fun i _ => (WithZero.exp_nsmul _ _).symm), prod_exp_eq]
    congr 1
    push_cast
    simp

theorem fracExists_of_smith : Smith → FracExists := by
  intro hS L _ _ ϖ n hϖ g hg
  obtain ⟨d, a, a', b, b', ha, ha', hb, hb', ea, eb, rfl⟩ := hS L ϖ n hϖ g hg
  have h := (hasLen_diagonal_zpow hϖ d).mul_mul ha ha' hb hb' ea eb
  rw [h.len_eq]
  exact h

end GlobalTheory.InertZeta
