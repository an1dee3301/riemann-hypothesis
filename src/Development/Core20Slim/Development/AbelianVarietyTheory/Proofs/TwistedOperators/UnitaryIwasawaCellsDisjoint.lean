module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryLeviNormalizesUnipotentRadical
public import Batteries.Logic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiJMulApply
public import Formalism.SatakeDualWeyl.StatementF
public import Init.Core
public import Init.Data.Fin.Basic
public import Init.Data.Fin.Lemmas
public import Init.Data.Int.Basic
public import Init.Data.Int.Lemmas
public import Init.Data.Int.Order
public import Init.Data.Nat.Basic
public import Init.Data.Nat.Lemmas
public import Init.Data.NeZero
public import Init.Data.Zero
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
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
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.GroupWithZero.Units.Lemmas
public import Mathlib.Algebra.GroupWithZero.WithZero
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Order.Monoid.Unbundled.TypeTags
public import Mathlib.Algebra.Quotient
public import Mathlib.Algebra.Ring.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.IsEmpty.Defs
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.RingTheory.Valuation.Integers
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Tactic.FieldSimp.Lemmas
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Valued.ValuationTopology

@[expose] public section

open Formalism.UG GlobalTheory.SatakeWeyl

namespace GlobalTheory.InertZeta

section

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {N : ℕ}

theorem blk_eq_zero_iff {l : Fin (N + 2)} : blk N l = 0 ↔ l = 0 := by
  rcases idx_cases l with rfl | ⟨j, rfl⟩ | rfl
  · simp
  · simp [mid_ne_zero]
  · simp [last_ne_zero]

theorem blk_eq_two_iff {l : Fin (N + 2)} : blk N l = 2 ↔ l = Fin.last (N + 1) := by
  rcases idx_cases l with rfl | ⟨j, rfl⟩ | rfl
  · simp [(last_ne_zero (N := N)).symm]
  · simp [mid_ne_last]
  · simp

theorem levi_mul_apply_zero {x : GU σ (N + 2)} (hx : x ∈ leviU σ (blk N)) (M : Matrix (Fin (N + 2)) (Fin (N + 2)) L)
    (j : Fin (N + 2)) : (mat x * M) 0 j = mat x 0 0 * M 0 j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single 0]
  · intro l _ hl
    rw [hx 0 l (by rw [blk_zero]; exact fun h => hl (blk_eq_zero_iff.1 h.symm)), zero_mul]
  · simp

theorem levi_mul_apply_last {x : GU σ (N + 2)} (hx : x ∈ leviU σ (blk N)) (M : Matrix (Fin (N + 2)) (Fin (N + 2)) L)
    (j : Fin (N + 2)) : (mat x * M) (Fin.last (N + 1)) j = mat x (Fin.last (N + 1)) (Fin.last (N + 1)) * M (Fin.last (N + 1)) j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.last (N + 1))]
  · intro l _ hl
    rw [hx _ l (by rw [blk_last]; exact fun h => hl (blk_eq_two_iff.1 h.symm)), zero_mul]
  · simp

theorem levi_mul_apply_mid {x : GU σ (N + 2)} (hx : x ∈ leviU σ (blk N)) (M : Matrix (Fin (N + 2)) (Fin (N + 2)) L)
    (i j : Fin (N + 2)) (k : Fin N) (hi : i = mid k) :
    (mat x * M) i j = ∑ l, mat x i (mid l) * M (mid l) j := by
  subst hi
  rw [Matrix.mul_apply, sum_idx (fun l => mat x (mid k) l * M l j), hx (mid k) 0 (by simp), hx (mid k) _ (by simp)]
  simp

end

theorem cosetInj : CosetInj := by
  intro L _ _ ϖ σ q N hU a a' g₀ g₀' m m' hm hm' u hu u' hu' hK
  have hσ : ∀ x, Valued.v (σ x) = Valued.v x := hU.2.1
  have hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ) := hU.2.2.2.1
  have hϖ0 : ϖ ≠ 0 := fun h => by rw [h, map_zero] at hϖ; exact WithZero.exp_ne_zero hϖ.symm
  have hvz : ∀ k : ℤ, Valued.v (ϖ ^ k) = WithZero.exp (-k) := fun k => by
    rw [map_zpow₀, hϖ, ← WithZero.exp_zsmul]; simp
  set n := m⁻¹ * m' with hn_def
  have hnL : n ∈ leviU σ (blk N) := mul_mem (inv_mem hm.1) hm'.1
  have hconj : n⁻¹ * u⁻¹ * n⁻¹⁻¹ ∈ radQ σ N :=
    (leviRad L σ (N + 2) (blk N) hσ n⁻¹ (inv_mem hnL) u⁻¹ (inv_mem hu)).1
  have he : (m * u)⁻¹ * (m' * u') = n * ((n⁻¹ * u⁻¹ * n⁻¹⁻¹) * u') := by
    rw [hn_def]; group
  have hnK : n ∈ KU σ (N + 2) :=
    (leviRad L σ (N + 2) (blk N) hσ n hnL _ (mul_mem hconj hu')).2 (he ▸ hK)
  have hint : ∀ i j, mat n i j ∈ intL L := (mem_KU_iff hσ n).1 hnK
  have hmn : mat m * mat n = mat m' := by rw [← mat_mul, hn_def, mul_inv_cancel_left]
  have h0 : ϖ ^ a * mat n 0 0 = ϖ ^ a' := by
    rw [← hm.2.1, ← hm'.2.1, ← hmn, levi_mul_apply_zero hm.1]
  have hl : ϖ ^ (-a) * mat n (Fin.last (N + 1)) (Fin.last (N + 1)) = ϖ ^ (-a') := by
    rw [← hm.2.2.1, ← hm'.2.2.1, ← hmn, levi_mul_apply_last hm.1]
  have hv0 := hint 0 0
  have hvl := hint (Fin.last (N + 1)) (Fin.last (N + 1))
  have e0 : mat n 0 0 = ϖ ^ (a' - a) := by
    rw [zpow_sub₀ hϖ0, ← h0]; field_simp
  have el : mat n (Fin.last (N + 1)) (Fin.last (N + 1)) = ϖ ^ (a - a') := by
    rw [show a - a' = -a' - -a by ring, zpow_sub₀ hϖ0, ← hl]; field_simp
  change Valued.v (mat n 0 0) ≤ 1 at hv0
  change Valued.v (mat n (Fin.last (N + 1)) (Fin.last (N + 1))) ≤ 1 at hvl
  rw [e0, hvz, ← WithZero.exp_zero, WithZero.exp_le_exp] at hv0
  rw [el, hvz, ← WithZero.exp_zero, WithZero.exp_le_exp] at hvl
  refine ⟨by omega, ?_⟩
  rw [mem_KU_iff hσ]
  have hmid : mat g₀ * Matrix.of (fun i j => mat n (mid i) (mid j)) = mat g₀' := by
    ext i j
    rw [← hm'.2.2.2, ← hmn, levi_mul_apply_mid hm.1 _ _ _ i rfl, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun l _ => by rw [hm.2.2.2]; rfl
  intro i j
  rw [mat_mul, ← hmid, ← Matrix.mul_assoc, mat_inv_mul, Matrix.one_mul]
  exact hint _ _

end GlobalTheory.InertZeta
