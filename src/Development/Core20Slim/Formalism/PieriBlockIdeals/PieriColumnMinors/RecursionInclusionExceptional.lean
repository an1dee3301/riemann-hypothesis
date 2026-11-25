module

public import Development.Core20Slim.Formalism.PieriBlockIdeals.StatementE
public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.AuxStatement14
public import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.RamBasic
public import Development.Core20Slim.Formalism.PieriBlockIdeals.PieriColumnMinors.ProdInitialMinorsMemDetSpan
public import Development.Core20Slim.Formalism.PieriBlockIdeals.BranchingBoundLastGradedOneRow
public import Development.Core20Slim.Formalism.PieriBlockIdeals.FactorialValuationSum
public import Development.Core20Slim.Formalism.PieriBlockIdeals.StatementLA
public import Development.Core20Slim.Formalism.RankGapBounds.CloudMinFalse
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Fin.Basic
public import Init.Data.Fin.Lemmas
public import Init.Data.Int.Basic
public import Init.Data.Int.Lemmas
public import Init.Data.Int.Order
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Filter
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Log
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Fin.Basic
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Order.Monotone.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

noncomputable section

open TensorProduct MvPolynomial
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder

namespace Formalism.CohomologicalDescent.E

open Formalism.UG Formalism.RankGapBounds.FormsTensorLocalization Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.LD Formalism.CohomologicalDescent.UnitNormBounds Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds











theorem res_anti_shift {N a : ℕ} {lam : ℕ → ℕ} (h : Antitone (res N lam)) :
    Antitone (res (N - a) (fun i => lam (a + i))) := by
  intro i j hij
  have hi : a + i.val < N := by have := i.isLt; omega
  have hj : a + j.val < N := by have := j.isLt; omega
  have hle : (⟨a + i.val, hi⟩ : Fin N) ≤ ⟨a + j.val, hj⟩ := by
    rw [Fin.mk_le_mk]
    have := Fin.le_iff_val_le_val.mp hij
    omega
  exact h hle

theorem exZ_rank_le_one {N : ℕ} (hN : N ≤ 1) (ν : Fin N → ℕ) (l : ℕ) (hl : l.Prime) :
    LA.exZ N N le_rfl ν l = 0 := by
  have hanti : Antitone ν := by
    intro i j _
    have hi := i.isLt
    have hj := j.isLt
    have : i = j := Fin.ext (by omega)
    rw [this]
  have h := LA.lattice_z_rank_le_two N N le_rfl (by omega) ν hanti l hl
  have he : Formalism.RankGapBounds.JumpSetsAlt.eExp (LA.lamU N N ν) l = 0 := by
    unfold Formalism.RankGapBounds.JumpSetsAlt.eExp
    apply Finset.sum_eq_zero
    intro p hp
    simp only [Formalism.RankGapBounds.JumpSetsAlt.posPairs, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    have h1 := p.1.isLt
    have h2 := p.2.isLt
    have h3 : p.1.val < p.2.val := hp
    omega
  rw [he] at h
  exact Nat.le_zero.mp (Nat.sInf_le h)

theorem exZ_le_of_exCut (hC : ExCut) (l : ℕ) (hl : l.Prime) (w : ℕ) :
    ∀ (N : ℕ) (lam : ℕ → ℕ), Antitone (res N lam) → ∀ lo : ℤ,
      (∀ a < N, lo ≤ UN N lam a ∧ UN N lam a ≤ lo + (w : ℤ)) →
      LA.exZ N N le_rfl (res N lam) l ≤ N.choose 2 * Nat.log l w := by
  intro N
  induction N with
  | zero =>
    intro lam _ lo _
    rw [exZ_rank_le_one (by norm_num) (res 0 lam) l hl]
    exact Nat.zero_le _
  | succ n ih =>
    intro lam hA lo hb

    have hcut : LA.exZ (n + 1) (n + 1) le_rfl (res (n + 1) lam) l ≤
        LA.exZ 1 1 le_rfl (res 1 lam) l +
          LA.exZ n n le_rfl (res n (fun i => lam (1 + i))) l + 1 * n * Nat.log l w :=
      hC (n + 1) lam hA l hl lo w hb 1 (by omega)
    have h1 : LA.exZ 1 1 le_rfl (res 1 lam) l = 0 := exZ_rank_le_one le_rfl _ l hl
    have hA' : Antitone (res n (fun i => lam (1 + i))) := res_anti_shift (a := 1) hA
    have hb' : ∀ a < n, lo ≤ UN n (fun i => lam (1 + i)) a ∧
        UN n (fun i => lam (1 + i)) a ≤ lo + (w : ℤ) := by
      intro a ha
      have hba := hb (1 + a) (by omega)
      have e : UN n (fun i => lam (1 + i)) a = UN (n + 1) lam (1 + a) := by
        simp only [UN]
        push_cast
        ring
      rw [e]
      exact hba
    have hrest := ih (fun i => lam (1 + i)) hA' lo hb'
    have hch : (n + 1).choose 2 = n.choose 2 + n := by
      have h2 := Nat.choose_succ_succ n 1
      rw [Nat.choose_one_right] at h2
      exact h2.trans (Nat.add_comm _ _)
    rw [h1] at hcut
    rw [hch, Nat.add_mul]
    have hstep : 0 + LA.exZ n n le_rfl (res n (fun i => lam (1 + i))) l + 1 * n * Nat.log l w ≤
        n.choose 2 * Nat.log l w + n * Nat.log l w := by
      rw [zero_add, one_mul]
      exact Nat.add_le_add_right hrest _
    exact le_trans hcut hstep

theorem exIntervalLt_of_exCut : ExCut → ExIntervalLt := by
  intro hC N lam hA l hl lo w hb
  have h := exZ_le_of_exCut hC l hl w N lam hA lo hb
  refine ⟨h, fun hw => ?_⟩
  have h0 : Nat.log l w = 0 := Nat.log_of_lt hw
  rw [h0, mul_zero] at h
  exact Nat.le_zero.mp h









end Formalism.CohomologicalDescent.E
