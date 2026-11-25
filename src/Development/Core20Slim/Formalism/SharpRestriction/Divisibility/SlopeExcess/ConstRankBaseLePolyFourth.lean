module

public import Formalism.SharpRestriction.ElevenLe
public import Formalism.LocalRingCardinality.KernelPlaceMeanBound
public import Formalism.LocalRingCardinality.DataParams
public import Formalism.SharpRestriction.ParConsts
public import Formalism.SharpRestriction.ParamsHeightRankConstant
public import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.FourMulQLeCondN
public import Batteries.Classes.RatCast
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataKap
public import Formalism.LocalRingCardinality.DataParams₂
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.NeZero
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.Group.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Ring.Unbundled.Basic
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Order.ZeroLEOne
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.Real.Star
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Cast.Order.Basic
public import Mathlib.Data.Nat.Cast.Order.Ring
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Rat.Cast.CharZero
public import Mathlib.Data.Rat.Cast.Defs
public import Mathlib.Logic.Function.Defs
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Tactic.CancelDenoms.Core
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.Linarith.Preprocessing
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Positivity.Core
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Tactic.Ring.RingNF

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.DIV.Proofs.HHParts

open Formalism.BasicNotions Formalism.MainNotions

variable {D : D7} (L : SizeData₂ D)

def _root_.Formalism.MainNotions.DIV.Proofs.szPol : ℝ := 1 + (D.R.f : ℝ) + D.R.k + D.R.m + D.R.t + (D.R.N D.R.m : ℝ) + L.sc.L

theorem sc_x_pos : 0 < L.sc.x := lt_trans one_pos L.sc.one_lt_alt

theorem sc_L_pos : 0 < L.sc.L := Real.rpow_pos_of_pos (sc_x_pos L) _

theorem one_le_szPol : 1 ≤ szPol L := by
  unfold szPol
  have h1 : (0:ℝ) ≤ L.sc.L := (sc_L_pos L).le
  have : (0:ℝ) ≤ (D.R.f:ℝ) + D.R.k + D.R.m + D.R.t + (D.R.N D.R.m : ℝ) := by positivity
  linarith

theorem f_le : (D.R.f : ℝ) ≤ szPol L := by
  unfold szPol; have := (sc_L_pos L).le; have : (0:ℝ) ≤ D.R.k + D.R.m + D.R.t + (D.R.N D.R.m : ℝ) := by positivity
  linarith
theorem k_le : (D.R.k : ℝ) ≤ szPol L := by
  unfold szPol; have := (sc_L_pos L).le; have : (0:ℝ) ≤ D.R.f + D.R.m + D.R.t + (D.R.N D.R.m : ℝ) := by positivity
  linarith
theorem m_le : (D.R.m : ℝ) ≤ szPol L := by
  unfold szPol; have := (sc_L_pos L).le; have : (0:ℝ) ≤ D.R.f + D.R.k + D.R.t + (D.R.N D.R.m : ℝ) := by positivity
  linarith
theorem t_le : (D.R.t : ℝ) ≤ szPol L := by
  unfold szPol; have := (sc_L_pos L).le; have : (0:ℝ) ≤ D.R.f + D.R.k + D.R.m + (D.R.N D.R.m : ℝ) := by positivity
  linarith
theorem N_le : (D.R.N D.R.m : ℝ) ≤ szPol L := by
  unfold szPol; have := (sc_L_pos L).le; have : (0:ℝ) ≤ D.R.f + D.R.k + D.R.m + (D.R.t : ℝ) := by positivity
  linarith
theorem L_le : L.sc.L ≤ szPol L := by
  unfold szPol; have : (0:ℝ) ≤ D.R.f + D.R.k + D.R.m + (D.R.t : ℝ) + (D.R.N D.R.m : ℝ) := by positivity
  linarith


theorem nV_le : (D.R.nV : ℝ) ≤ szPol L := by
  have h := congrArg (fun q : ℚ => (q : ℝ)) (Formalism.BasicNotions.DV.nV_cast D.R)
  push_cast at h
  rw [h]
  unfold szPol; have := (sc_L_pos L).le; have : (0:ℝ) ≤ D.R.f + (D.R.N D.R.m : ℝ) := by positivity
  linarith

theorem one_le_b : 1 ≤ L.sc.b := by
  unfold Scale.b; exact Real.one_le_exp (sc_L_pos L).le

theorem x_le_k (h : SizeK L) : L.sc.x ≤ D.R.k := by
  have hx := L.sc.one_lt_alt
  have he := L.sc.eps_pos
  have : L.sc.x ≤ L.sc.x ^ (9 / 2 + 10 * L.sc.eps - szTh L) := by
    conv_lhs => rw [← Real.rpow_one L.sc.x]
    apply Real.rpow_le_rpow_of_exponent_le hx.le
    unfold szTh; linarith [L.sc.eps_lt]
  exact this.trans h.1

theorem x_le (h : SizeK L) : L.sc.x ≤ szPol L := (x_le_k L h).trans (k_le L)

theorem a_nonneg : 0 ≤ L.sc.a := by
  unfold Scale.a; exact mul_nonneg (sc_x_pos L).le (by linarith [one_le_b L])

theorem a_le (h : SizeK L) : L.sc.a ≤ szPol L * L.sc.b := by
  unfold Scale.a; exact mul_le_mul_of_nonneg_right (x_le L h) (by linarith [one_le_b L])

theorem one_le_X' : 1 ≤ L.sc.X' := by
  unfold Scale.X'; exact Real.one_le_exp (Real.rpow_pos_of_pos (sc_x_pos L) _).le

theorem b'_nonneg : 0 ≤ L.sc.b' := by
  unfold Scale.b'; exact div_nonneg (a_nonneg L) (by linarith [one_le_X' L])

theorem b'_le_a : L.sc.b' ≤ L.sc.a := by
  unfold Scale.b'; exact div_le_self (a_nonneg L) (one_le_X' L)

variable {L}

theorem n_pos (hN : SizeN L) : 1 ≤ (D.R.n : ℝ) := by
  have h := lt_of_lt_of_le (Real.rpow_pos_of_pos (sc_x_pos L) _) hN.1
  have : 0 < D.R.n := by exact_mod_cast h
  exact_mod_cast this

theorem f_eq : (D.R.f : ℝ) = 2 * D.R.n := by unfold Ranks.f; push_cast; ring

theorem k_one (hK : SizeK L) : 1 ≤ (D.R.k : ℝ) := by linarith [x_le_k L hK, L.sc.one_lt_alt]

theorem w''_nonneg : 0 ≤ L.sc.w'' D.R.n := by
  unfold Scale.w''; exact div_nonneg (b'_nonneg L) (mul_nonneg (sc_x_pos L).le (Nat.cast_nonneg _))

theorem w''_le (hN : SizeN L) : L.sc.w'' D.R.n ≤ L.sc.b' := by
  unfold Scale.w''
  apply div_le_self (b'_nonneg L)
  have := n_pos hN; have := L.sc.one_lt_alt; nlinarith



theorem eta_le (hN : SizeN L) (hK : SizeK L) (hEta : SizeEta L) : L.etaSz ≤ L.sc.b := by
  refine hEta.2.1.trans (div_le_self (by linarith [one_le_b L]) ?_)
  have ht : (1:ℝ) ≤ D.R.t := L.t_win.1
  have hf : (1:ℝ) ≤ D.R.f := by rw [f_eq]; linarith [n_pos hN]
  have hk := k_one hK
  have h1 : (1:ℝ) ≤ (D.R.t : ℝ) ^ 3 := one_le_pow₀ ht
  have h2 : (1:ℝ) ≤ (D.R.k : ℝ) ^ 3 := one_le_pow₀ hk
  calc (1:ℝ) = 1 * 1 * 1 := by ring
    _ ≤ (D.R.t : ℝ) ^ 3 * D.R.f * (D.R.k : ℝ) ^ 3 := by gcongr

theorem delta1_le : L.sc.delta1 ≤ 1 := by
  unfold Scale.delta1
  exact Real.rpow_le_one_of_one_le_of_nonpos L.sc.one_lt_alt.le (by linarith [L.sc.eps_pos])


theorem xth_le : L.sc.x ^ szTh L ≤ L.sc.L := by
  unfold Scale.L szTh
  apply Real.rpow_le_rpow_of_exponent_le L.sc.one_lt_alt.le
  linarith [L.sc.eps_pos]

theorem LaG_le (hLa : SizeLa L) : L.LaG ≤ L.sc.L ^ 2 := by
  refine hLa.2.trans ?_
  rw [Real.rpow_add (sc_x_pos L), sq]
  exact mul_le_mul_of_nonneg_left xth_le (Real.rpow_pos_of_pos (sc_x_pos L) _).le

theorem LaG_pos (hLa : SizeLa L) : 0 < L.LaG := lt_of_lt_of_le (Real.rpow_pos_of_pos (sc_x_pos L) _) hLa.1

theorem bT_nonneg (t : D.host.TT) : 0 ≤ (L.bT t : ℝ) := (b'_nonneg L).trans (L.bT_ge t)

theorem bT_le (hK : SizeK L) (hLa : SizeLa L) (hBot : SizeBot L) (t : D.host.TT) :
    (L.bT t : ℝ) ≤ 2 * szPol L ^ 5 * L.sc.b := by
  have hP := one_le_szPol L
  have hb := one_le_b L
  have hk := k_one hK
  have hNs : szNst L ≤ szPol L := by
    unfold szNst; refine le_trans ?_ (f_le L); rw [f_eq]
    have := delta1_le (L := L); have h0 : (0:ℝ) ≤ D.R.n := Nat.cast_nonneg _
    nlinarith
  have hNs0 : 0 ≤ szNst L := by
    unfold szNst; have : 0 ≤ L.sc.delta1 := (Real.rpow_pos_of_pos (sc_x_pos L) _).le
    positivity
  have hxe : L.sc.x ^ L.sc.eps ≤ szPol L := L_le L
  have hxe0 : 0 ≤ L.sc.x ^ L.sc.eps := (sc_L_pos L).le
  have hG : L.LaG ≤ szPol L ^ 2 := (LaG_le hLa).trans (pow_le_pow_left₀ (sc_L_pos L).le (L_le L) 2)
  have hG0 := (LaG_pos hLa).le
  have hb' : L.sc.b' ≤ szPol L * L.sc.b := (b'_le_a L).trans (a_le L hK)
  have hb'0 := b'_nonneg L
  have e1 : szNst L * L.sc.x ^ L.sc.eps * L.LaG * L.sc.b' ≤ szPol L * szPol L * szPol L ^ 2 * (szPol L * L.sc.b) := by
    apply mul_le_mul _ hb' hb'0 (by positivity)
    apply mul_le_mul _ hG hG0 (by positivity)
    exact mul_le_mul hNs hxe hxe0 (by positivity)
  have e2 : szNst L * L.sc.x ^ L.sc.eps * L.LaG * L.sc.b' / D.R.k ≤ szNst L * L.sc.x ^ L.sc.eps * L.LaG * L.sc.b' :=
    div_le_self (by positivity) hk
  have := hBot t
  have h5 : szPol L * L.sc.b ≤ szPol L ^ 5 * L.sc.b := by
    apply mul_le_mul_of_nonneg_right _ (by linarith)
    calc szPol L = szPol L ^ 1 := (pow_one _).symm
      _ ≤ szPol L ^ 5 := pow_le_pow_right₀ hP (by norm_num)
  have h6 : szPol L * szPol L * szPol L ^ 2 * (szPol L * L.sc.b) = szPol L ^ 5 * L.sc.b := by ring
  linarith


theorem q_pos (hQD : SizeQD L) : 1 < (D.host.q : ℝ) := by
  have h := lt_of_lt_of_le (Real.rpow_pos_of_pos (sc_x_pos L) _) hQD.1
  by_contra hc; replace hc := not_lt.1 hc
  have : Real.log (D.host.q : ℝ) ≤ 0 := Real.log_nonpos (Nat.cast_nonneg _) hc
  linarith

theorem d_pos (hQD : SizeQD L) : 1 < (D.host.d : ℝ) := by
  have h := lt_of_lt_of_le (Real.rpow_pos_of_pos (sc_x_pos L) _) hQD.2.2.2.1
  by_contra hc; replace hc := not_lt.1 hc
  have : Real.log (D.host.d : ℝ) ≤ 0 := Real.log_nonpos (Nat.cast_nonneg _) hc
  linarith

theorem log_rdE_bounds (hN : SizeN L) (hQD : SizeQD L) :
    0 ≤ Real.log D.host.rdE ∧ Real.log D.host.rdE ≤ 2 * szPol L := by
  have hq := q_pos hQD; have hd := d_pos hQD
  obtain ⟨-, -, hq2, -, hd2, -, hr1, -⟩ := hQD
  have hn := n_pos hN
  refine ⟨Real.log_nonneg hr1, ?_⟩
  have e1 := UpperTheory.Ram.Rd.log_rdE_le D.host
  have e2 : Real.log (D.R.n : ℝ) ≤ D.R.n := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < D.R.n by positivity); linarith
  have ex : L.sc.x ^ (L.sc.eps / 5 + szTh L) ≤ L.sc.L := by
    unfold Scale.L szTh
    apply Real.rpow_le_rpow_of_exponent_le L.sc.one_lt_alt.le
    linarith [L.sc.eps_pos]
  have := f_le L; have := L_le L; rw [f_eq] at *
  linarith

theorem La_bounds (hN : SizeN L) (hK : SizeK L) (hQD : SizeQD L) : 0 ≤ L.La ∧ L.La ≤ 4 * szPol L := by
  obtain ⟨h0, h1⟩ := log_rdE_bounds hN hQD
  have hr : 1 ≤ D.host.rdE := hQD.2.2.2.2.2.2.1
  have hb := one_le_b L
  have hx := L.sc.one_lt_alt
  unfold SizeData₂.La Scale.a
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)]
  have lb : Real.log L.sc.b = L.sc.L := by unfold Scale.b; exact Real.log_exp _
  rw [lb]
  have lx0 : 0 ≤ Real.log L.sc.x := Real.log_nonneg hx.le
  have lx1 : Real.log L.sc.x ≤ L.sc.x := (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
  have := x_le L hK; have := L_le L; have := (sc_L_pos L).le
  constructor <;> linarith

theorem pow_mono_P {a b : ℕ} (h : a ≤ b) : szPol L ^ a ≤ szPol L ^ b := pow_le_pow_right₀ (one_le_szPol L) h

theorem P_le_pow {b : ℕ} (h : 1 ≤ b) : szPol L ≤ szPol L ^ b := by
  calc szPol L = szPol L ^ 1 := (pow_one _).symm
    _ ≤ szPol L ^ b := pow_mono_P h

theorem nV_one (hK : SizeK L) : 1 ≤ (D.R.nV : ℝ) := by
  have h := congrArg (fun q : ℚ => (q : ℝ)) (Formalism.BasicNotions.DV.nV_cast D.R)
  push_cast at h
  rw [h]
  have := k_one hK
  have : (2:ℝ) ≤ D.R.m := by exact_mod_cast D.R.two_le_m
  have : (0:ℝ) ≤ D.R.t := Nat.cast_nonneg _
  linarith



theorem wj_eq (τ : D.what₂.Tau) (q : Fin D.R.m) : wj D (q.1 + 1) τ = (((D.hc τ).e q : ℚ) : ℝ) := by
  unfold wj; simp

theorem top_or (τ : D.what₂.Tau) :
    (∃ t : D.host.TT, (D.eTau τ : D.R.GG) = D.R.tau1 t) ∨
      (D.eTau τ : D.R.GG) ∉ D.host.topPlaces := by
  by_cases h : (D.eTau τ : D.R.GG) ∈ D.host.topPlaces
  · left
    obtain ⟨a, ha, he⟩ := Finset.mem_image.1 h
    exact ⟨⟨a, ha⟩, he.symm⟩
  · exact Or.inr h

theorem Pb_le (k : ℕ) (hk : 1 ≤ k) : szPol L * L.sc.b ≤ szPol L ^ k * L.sc.b :=
  mul_le_mul_of_nonneg_right (P_le_pow hk) (by linarith [one_le_b L])

theorem b_le_poly_fifth_mul_b : L.sc.b ≤ szPol L ^ 5 * L.sc.b := by
  have : (1:ℝ) ≤ szPol L ^ 5 := one_le_pow₀ (one_le_szPol L)
  have := one_le_b L; nlinarith

theorem e_bounds (hN : SizeN L) (hK : SizeK L) (hLa : SizeLa L) (hBot : SizeBot L) (hEta : SizeEta L)
    (τ : D.what₂.Tau) (q : Fin D.R.m) :
    0 ≤ (((D.hc τ).e q : ℚ) : ℝ) ∧ (((D.hc τ).e q : ℚ) : ℝ) ≤ 4 * szPol L ^ 5 * L.sc.b := by
  rw [← wj_eq]
  have hb := one_le_b L
  have he := eta_le hN hK hEta
  have he0 := L.etaSz_pos.le
  have h5 := b_le_poly_fifth_mul_b (L := L)
  have hPb := Pb_le (L := L) 5 (by norm_num)
  rcases top_or τ with ⟨t, ht⟩ | hnt
  · obtain ⟨w1, w2⟩ := L.win_top (q.1 + 1) (by omega) (by omega) τ t ht
    have hbt := bT_le hK hLa hBot t
    have hbt0 := bT_nonneg (L := L) t
    have hx : L.sc.b' / L.sc.x ≤ L.sc.b' := div_le_self (b'_nonneg L) L.sc.one_lt_alt.le
    have hx0 : 0 ≤ L.sc.b' / L.sc.x := div_nonneg (b'_nonneg L) (sc_x_pos L).le
    have hb' : L.sc.b' ≤ szPol L * L.sc.b := (b'_le_a L).trans (a_le L hK)
    constructor <;> linarith
  · by_cases hth : (D.eTau τ : D.R.GG) ∈ D.host.thickPlaces
    · obtain ⟨w1, w2⟩ := L.win_thick (q.1 + 1) (by omega) (by omega) τ hth
      constructor <;> linarith
    · have hthin : D.host.IsThin (D.eTau τ : D.R.GG) := ⟨(D.eTau τ).2, hnt, hth⟩
      obtain ⟨w1, w2⟩ := L.win_thin (q.1 + 1) (by omega) (by omega) τ hthin
      have h1 := w''_nonneg (L := L)
      have h2 : L.sc.w'' D.R.n ≤ szPol L * L.sc.b := (w''_le hN).trans ((b'_le_a L).trans (a_le L hK))
      constructor <;> linarith






















theorem card_Tau : ((Finset.univ : Finset D.what₂.Tau).card : ℝ) ≤ szPol L := by
  rw [Finset.card_univ, D.what₂.card_Tau]; exact f_le L


theorem poly_pow_mul_b_le_ninth {a : ℕ} (ha : a ≤ 9) : szPol L ^ a * L.sc.b ≤ szPol L ^ 9 * L.sc.b :=
  mul_le_mul_of_nonneg_right (pow_mono_P ha) (by linarith [one_le_b L])






theorem _root_.Formalism.MainNotions.DIV.Proofs.szPol_le_rpow (hS : SizesAt L) (hx : 9 ≤ L.sc.x) : szPol L ≤ L.sc.x ^ (max L.Ct 5 + 3) := by
  obtain ⟨hN, hM, hK, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := hS
  have hx0 : 0 < L.sc.x := sc_x_pos L
  have hx1 : 1 ≤ L.sc.x := L.sc.one_lt_alt.le
  have he := L.sc.eps_pos
  have he' := L.sc.eps_lt
  set c := max L.Ct 5 with hc
  have hc5 : 5 ≤ c := le_max_right _ _
  have hct : L.Ct ≤ c := le_max_left _ _
  have rp : ∀ a b : ℝ, a ≤ b → L.sc.x ^ a ≤ L.sc.x ^ b := fun a b h => Real.rpow_le_rpow_of_exponent_le hx1 h
  set X := L.sc.x ^ (c + 2) with hX
  have hX1 : 1 ≤ X := Real.one_le_rpow hx1 (by linarith)
  have hth : szTh L ≤ L.sc.eps / 100 := le_refl _
  have hth0 : 0 ≤ szTh L := by unfold szTh; linarith
  have hxx : ∀ a b : ℝ, L.sc.x ^ a * L.sc.x ^ b = L.sc.x ^ (a + b) := fun a b => (Real.rpow_add hx0 a b).symm

  have hf : (D.R.f : ℝ) ≤ X := by
    rw [f_eq]
    have h1 : 2 * (D.R.n : ℝ) ≤ L.sc.x ^ (1:ℝ) * L.sc.x ^ (2 + 8 * L.sc.eps + szTh L) := by
      rw [Real.rpow_one]; nlinarith [hN.2]
    rw [hxx] at h1
    exact h1.trans (rp _ _ (by unfold szTh at *; linarith))
  have hk : (D.R.k : ℝ) ≤ X := hK.2.trans (rp _ _ (by unfold szTh at *; linarith))
  have hm : (D.R.m : ℝ) ≤ L.sc.x ^ (szTh L + 1 / 2) := by
    refine hM.2.trans ?_
    have hs : Real.sqrt (L.sc.x * L.sc.delta1) ≤ L.sc.x ^ (1 / 2 : ℝ) := by
      rw [← Real.sqrt_eq_rpow]
      apply Real.sqrt_le_sqrt
      have := delta1_le (L := L)
      nlinarith
    rw [← hxx]
    exact mul_le_mul_of_nonneg_left hs (Real.rpow_pos_of_pos hx0 _).le
  have hmX : (D.R.m : ℝ) ≤ X := hm.trans (rp _ _ (by unfold szTh at *; linarith))
  have ht : (D.R.t : ℝ) ≤ L.sc.x ^ c := L.t_win.2.trans (rp _ _ hct)
  have htX : (D.R.t : ℝ) ≤ X := ht.trans (rp _ _ (by linarith))
  have hxc1 : 1 ≤ L.sc.x ^ c := Real.one_le_rpow hx1 (by linarith)
  have hNX : (D.R.N D.R.m : ℝ) ≤ 2 * X := by
    have hNe : (D.R.N D.R.m : ℝ) = D.R.k + D.R.m * (D.R.t + 1) := by unfold Ranks.N; push_cast; ring
    have h1 : (D.R.t : ℝ) + 1 ≤ L.sc.x ^ (1:ℝ) * L.sc.x ^ c := by rw [Real.rpow_one]; nlinarith
    rw [hxx] at h1
    have h2 : (D.R.m : ℝ) * (D.R.t + 1) ≤ L.sc.x ^ (szTh L + 1 / 2) * L.sc.x ^ (1 + c) :=
      mul_le_mul hm h1 (by positivity) (Real.rpow_pos_of_pos hx0 _).le
    rw [hxx] at h2
    have h3 : L.sc.x ^ (szTh L + 1 / 2 + (1 + c)) ≤ X := rp _ _ (by unfold szTh at *; linarith)
    rw [hNe]; linarith
  have hL : L.sc.L ≤ X := rp _ _ (by linarith)
  have hsum : szPol L ≤ 8 * X := by unfold szPol; linarith
  have h8 : 8 * X ≤ L.sc.x ^ (1:ℝ) * X := by rw [Real.rpow_one]; nlinarith
  rw [hX, hxx] at h8
  rw [hX] at hsum
  exact hsum.trans (h8.trans (le_of_eq (by ring_nf)))

theorem _root_.Formalism.MainNotions.DIV.Proofs.bPol_le (hS : SizesAt L) (C : ℝ) (e : ℕ) (hx : max 9 C ≤ L.sc.x) :
    C * szPol L ^ e * L.sc.b ≤ L.sc.x ^ ((e : ℝ) * (max L.Ct 5 + 3) + 1) * L.sc.b := by
  have hx0 : 0 < L.sc.x := sc_x_pos L
  have hx9 : 9 ≤ L.sc.x := (le_max_left _ _).trans hx
  have hxC : C ≤ L.sc.x := (le_max_right _ _).trans hx
  have hp := szPol_le_rpow hS hx9
  have hP := one_le_szPol L
  have hb := one_le_b L
  have h1 : szPol L ^ e ≤ L.sc.x ^ ((e : ℝ) * (max L.Ct 5 + 3)) := by
    calc szPol L ^ e ≤ (L.sc.x ^ (max L.Ct 5 + 3)) ^ e := pow_le_pow_left₀ (by linarith) hp e
      _ = L.sc.x ^ ((e : ℝ) * (max L.Ct 5 + 3)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le, mul_comm]
  have h2 : C * szPol L ^ e ≤ L.sc.x * szPol L ^ e := mul_le_mul_of_nonneg_right hxC (by positivity)
  have h3 : L.sc.x * szPol L ^ e ≤ L.sc.x * L.sc.x ^ ((e : ℝ) * (max L.Ct 5 + 3)) :=
    mul_le_mul_of_nonneg_left h1 hx0.le
  have h4 : L.sc.x * L.sc.x ^ ((e : ℝ) * (max L.Ct 5 + 3)) = L.sc.x ^ ((e : ℝ) * (max L.Ct 5 + 3) + 1) := by
    rw [Real.rpow_add hx0, Real.rpow_one, mul_comm]
  exact mul_le_mul_of_nonneg_right (h2.trans (h3.trans h4.le)) (by linarith)




end Formalism.MainNotions.DIV.Proofs.HHParts

end
