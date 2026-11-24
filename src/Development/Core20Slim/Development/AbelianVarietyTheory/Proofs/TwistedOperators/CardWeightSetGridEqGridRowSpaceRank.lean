module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NodeYPredEqChainVertexAtRowZeroLast
public import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.HighestWeightBelow
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridMinimalGapEqChiGridGapGammaOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.LeastSplitAuxiliaryPrimeThetaChainSpec
public import Development.AbelianVarietyTheory.Definitions.Foundations.StrictInterlaceIffDescEnum
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Fin.Lemmas
public import Init.Data.Int.Basic
public import Init.Data.Int.Lemmas
public import Init.Data.Int.Order
public import Init.Data.Nat.Basic
public import Init.Data.NeZero
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Prelude
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.Group.Abs
public import Mathlib.Algebra.Order.Group.Defs
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.Ring.Canonical
public import Mathlib.Algebra.Order.Ring.Cast
public import Mathlib.Algebra.Order.Ring.Rat
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Ring.Unbundled.Rat
public import Mathlib.Algebra.Order.Star.Rat
public import Mathlib.Algebra.Order.ZeroLEOne
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Algebra.Star.Rat
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Disjoint
public import Mathlib.Data.Finset.Empty
public import Mathlib.Data.Finset.Lattice.Basic
public import Mathlib.Data.Int.Cast.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Cast.Order.Basic
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Rat.Defs
public import Mathlib.Data.Rat.Floor
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Disjoint
public import Mathlib.Order.Lattice
public import Mathlib.Tactic.CancelDenoms.Core
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.IndefR Formalism.IndefR.Links

namespace GlobalTheory.Grid

theorem card_weightX_grid : ∀ (D : D7), HostHyp D → ∀ (τ : D.what₂.Tau) (j : ℕ), 1 ≤ j → j ≤ D.R.m →
    ((GlobalTheory.Grid.grid D τ).weightX j).card = GlobalTheory.Grid.rkX D j := by
  intro D _ τ j _ hj
  have hcen : GlobalTheory.Grid.cen D τ = GlobalTheory.ChiGrid.cen D 1 τ := by
    funext i
    unfold GlobalTheory.Grid.cen GlobalTheory.ChiGrid.cen GlobalTheory.Grid.gridOf
    rw [GlobalTheory.GridJoin.gap_eq_chiGap D]
    rfl
  have hg : GlobalTheory.Grid.grid D τ = GlobalTheory.ChiGrid.num D 1 τ := by
    unfold GlobalTheory.Grid.grid GlobalTheory.Grid.gridOf GlobalTheory.ChiGrid.num
    rw [hcen, GlobalTheory.GridJoin.gap_eq_chiGap D]
    rfl
  rw [hg]
  let Γ := GlobalTheory.ChiGrid.num D 1 τ
  have num_e {l : ℕ} (h1 : 1 ≤ l) (h2 : l ≤ D.R.m) : (((Γ).e l : ℤ) : ℚ) = (D.hc τ).e ⟨l - 1, by omega⟩ := by
    obtain ⟨l, rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
    exact GlobalTheory.SignedHC.GridData.extend_cast 1 (D.hc τ).e_int ⟨l, by omega⟩
  
  have num_b {l : ℕ} (h1 : 1 ≤ l) (h2 : l ≤ D.R.m) : (((Γ).b l : ℤ) : ℚ) = (D.hc τ).b ⟨l - 1, by omega⟩ := by
    obtain ⟨l, rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
    exact GlobalTheory.SignedHC.GridData.extend_cast 1 (D.hc τ).b_int ⟨l, by omega⟩
  
  have num_v {i : ℕ} (h1 : 2 ≤ i) (h2 : i ≤ D.R.k) : (((Γ).v i : ℤ) : ℚ) = (D.hc τ).v ⟨i - 2, by omega⟩ := by
    obtain ⟨i, rfl⟩ : ∃ i', i = i' + 2 := ⟨i - 2, by omega⟩
    exact GlobalTheory.SignedHC.GridData.extend_cast 2 (D.hc τ).v_int ⟨i, by omega⟩
  
  have num_be {l : ℕ} (h1 : 1 ≤ l) (h2 : l ≤ D.R.m) : ((D.R.t : ℚ) + 3) / 2 ≤ ((Γ).e l : ℚ) - (Γ).b l := by
    rw [num_e h1 h2, num_b h1 h2]
    exact (D.hc τ).gap_be _
  
  have num_eb {l : ℕ} (h1 : 1 ≤ l) (h2 : l + 1 ≤ D.R.m) : ((D.R.t : ℚ) + 3) / 2 ≤ ((Γ).b (l + 1) : ℚ) - (Γ).e l := by
    rw [num_e h1 (by omega), num_b (by omega) h2]
    obtain ⟨l, rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
    exact (D.hc τ).gap_eb ⟨l, by omega⟩ (by simpa using (by omega : l + 1 < D.R.m))
  
  have num_e_lt {l l' : ℕ} (h1 : 1 ≤ l) (h : l < l') (h2 : l' ≤ D.R.m) : (D.R.t : ℚ) + 3 + (Γ).e l ≤ (Γ).e l' := by
    induction l', h using Nat.le_induction with
    | base =>
      linarith [num_be (l := l + 1) (by omega) h2, num_eb h1 h2]
    | succ n hn ih =>
      have := ih (by omega)
      have e1 := num_be (l := n + 1) (by omega) h2
      have e2 := num_eb (l := n) (by omega) h2
      have : (0 : ℚ) ≤ D.R.t := by positivity
      linarith
  
  have num_cloud {i : ℕ} (h1 : 2 ≤ i) (h2 : i ≤ D.R.k) : -((Γ).b 1 : ℚ) + 1 ≤ (Γ).v i := by
    have hm : 1 ≤ D.R.m := by have := D.R.two_le_m; omega
    have hk : 2 ≤ D.R.k := by omega
    have base : -((Γ).b 1 : ℚ) < (Γ).v D.R.k := by
      rw [num_v hk le_rfl, num_b le_rfl hm]
      have e1 := (D.hc τ).u_last_gt (by omega) (by omega)
      have e2 := (D.hc τ).v_gt_u ⟨D.R.k - 2, by omega⟩
      have e3 : (⟨D.R.k - 2 + 1, by omega⟩ : Fin D.R.k) = ⟨D.R.k - 1, by omega⟩ := Fin.ext (by simp only; omega)
      simp only [e3] at e2
      exact e1.trans e2
    have base' : -((Γ).b 1) < (Γ).v D.R.k := by exact_mod_cast base
    have step : (Γ).v D.R.k ≤ (Γ).v i := by
      rcases h2.eq_or_lt with rfl | h
      · exact le_rfl
      · exact ((Γ).v_anti i D.R.k h1 h le_rfl).le
    have : -((Γ).b 1) + 1 ≤ (Γ).v i := by omega
    exact_mod_cast this
  
  have a_le {i j : ℕ} (h : i ≤ j) : (Γ).a j ≤ (Γ).a i := by
    rcases h.eq_or_lt with rfl | h
    · exact le_rfl
    · have : (0 : ℚ) ≤ (Γ).ga := by positivity
      linarith [GlobalTheory.ChiGrid.a_add_le (G := Γ) h]
  
  have hblock {l : ℕ} {x : ℚ} (h : x ∈ (GlobalTheory.ChiGrid.num D 1 τ).blockMPlus l) :
      -((GlobalTheory.ChiGrid.num D 1 τ).e l : ℚ) - (D.R.t : ℚ) / 2 ≤ x ∧ x ≤ -((GlobalTheory.ChiGrid.num D 1 τ).e l : ℚ) + (D.R.t : ℚ) / 2 := by
    have h' := abs_le.1 (GlobalTheory.SignedHC.abs_sub_le_of_mem_block h)
    have e : (((GlobalTheory.ChiGrid.num D 1 τ).t + 1 : ℕ) : ℚ) = D.R.t + 1 := by push_cast; rfl
    rw [e] at h'
    constructor <;> linarith [h'.1, h'.2]
  have habove {j : ℕ} (hj : j + 1 ≤ D.R.m) {x y : ℚ} (hx : x ∈ (GlobalTheory.ChiGrid.num D 1 τ).weightX j) (hy : y ∈ (GlobalTheory.ChiGrid.num D 1 τ).blockMPlus (j + 1)) : y < x := by
    let Γ := GlobalTheory.ChiGrid.num D 1 τ
    have hm : 1 ≤ D.R.m := by omega
    have hk : 2 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
    have ht : (0 : ℚ) ≤ D.R.t := by positivity
    have hg : (0 : ℚ) ≤ Γ.ga := by positivity
    obtain ⟨y1, y2⟩ := hblock hy
    have hbe := num_be (l := 1) le_rfl hm
    have he1 : ((Γ.e 1 : ℚ)) ≤ Γ.e (j + 1) := by
      rcases Nat.eq_zero_or_pos j with rfl | h
      · exact le_rfl
      · linarith [num_e_lt (l := 1) (l' := j + 1) le_rfl (by omega) hj]
    have hlow : y < -(Γ.b 1 : ℚ) := by linarith
    have hc2 := num_cloud (i := 2) le_rfl hk
    have ham : Γ.a Γ.m = Γ.v 2 + Γ.ga + 1 / 2 := Γ.a_m
    rcases GlobalTheory.SignedHC.GridData.mem_weightX.1 hx with h | h | ⟨i, h1, h2, h⟩ | ⟨l, h1, h2, h⟩
    · obtain ⟨i, hi, rfl⟩ := GlobalTheory.SignedHC.GridData.mem_tops.1 h
      linarith [a_le hi]
    · obtain ⟨i, h1, h2, rfl⟩ := GlobalTheory.SignedHC.GridData.mem_cloudHalf.1 h
      have := num_cloud h1 h2
      simp only [GlobalTheory.SignedHC.GridData.vHalf]
      linarith
    · have := (GlobalTheory.ChiGrid.blockC'_between (GlobalTheory.ChiGrid.num_nearMid D 1 τ) (GlobalTheory.ChiGrid.odd_sLen D).pos (GlobalTheory.ChiGrid.sLen_lt_gap D 1) h1 h2 h).1
      linarith [a_le h2]
    · have := num_e_lt h1 (by omega : l < j + 1) hj
      have := (hblock h).1
      linarith
  have hcard : ∀ {j : ℕ}, j ≤ D.R.m → ((GlobalTheory.ChiGrid.num D 1 τ).weightX j).card = GlobalTheory.ChiGrid.rankX D j := by
    intro j hj
    induction j with
    | zero =>
      rw [GlobalTheory.ChiGrid.card_weightX_zero (GlobalTheory.ChiGrid.num_nearMid D 1 τ) (GlobalTheory.ChiGrid.odd_sLen D).pos (GlobalTheory.ChiGrid.sLen_lt_gap D 1)]
      simp [GlobalTheory.ChiGrid.rankX]; rfl
    | succ j ih =>
      rw [(GlobalTheory.ChiGrid.num D 1 τ).weightX_succ, Finset.card_union_of_disjoint
        (Finset.disjoint_left.2 fun x hx hy => (habove hj hx hy).ne rfl), ih (by omega)]
      have : ((GlobalTheory.ChiGrid.num D 1 τ).blockMPlus (j + 1)).card = D.R.t + 1 := GlobalTheory.SignedHC.card_block _ _
      rw [this]
      simp only [GlobalTheory.ChiGrid.rankX]
      ring
  rw [hcard hj]
  rfl

end GlobalTheory.Grid
