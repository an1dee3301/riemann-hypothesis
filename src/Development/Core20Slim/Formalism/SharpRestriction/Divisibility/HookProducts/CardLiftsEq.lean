module

public import Development.Core20Slim.Formalism.SharpRestriction.Divisibility.SlopeExcess.ConstRankBaseLePolyFourth
public import Formalism.SharpRestriction.GrowthBounds.TopChoiceBounds
public import Formalism.SharpRestriction.GrowthBounds.JointsLit
public import Formalism.SharpRestriction.GrowthBounds.LogarithmicSums.NotSingularOfCentral
public import Formalism.SharpRestriction.GrowthBounds.AdmissibleIntegers.FirstTermSizeBound
public import Formalism.SharpRestriction.Divisibility.WeightDegreeSizes

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.DIV.HookProducts.Row4

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.WeilJacquetShalikaLaw Formalism.MainNotions.WeightDegreeSizes

variable {D : D7} {L : SizeData₂ D}



theorem card_lifts_eq (D : D7) : ((SizeData₂.lifts D).card : ℝ) = D.R.m := by
  simp [SizeData₂.lifts]





open Formalism.MainNotions.DIV.Proofs.HHParts in
theorem logX_le (hN : SizeN L) (hK : SizeK L) :
    Real.log (L.sc.X'' D.R.n + 1) ≤ 4 * Formalism.MainNotions.DIV.Proofs.szPol L := by
  obtain ⟨hn1, hn2⟩ := hN
  obtain ⟨hk1, -⟩ := hK
  have hx1 := L.sc.one_lt_alt
  have he := L.sc.eps_pos
  have hx0 : 0 < L.sc.x := lt_trans zero_lt_one hx1
  have hnpos : 0 < (D.R.n : ℝ) := lt_of_lt_of_le (Real.rpow_pos_of_pos hx0 _) hn1
  have hX'1 : 1 ≤ L.sc.X' := by
    simp only [Scale.X']
    exact Real.one_le_exp (Real.rpow_nonneg hx0.le _)
  have hX'0 : 0 < L.sc.X' := lt_of_lt_of_le zero_lt_one hX'1
  have ha : 0 < L.sc.a := by
    simp only [Scale.a, Scale.b]
    exact mul_pos hx0 (Real.exp_pos _)
  have hXeq : L.sc.X'' D.R.n = L.sc.x * D.R.n * L.sc.X' := by
    simp only [Scale.X'', Scale.w'', Scale.b']
    field_simp [ha.ne', hX'0.ne', hx0.ne', hnpos.ne']
    try ring
  have hbound : L.sc.X'' D.R.n + 1 ≤ (L.sc.x + 1) * ((D.R.n : ℝ) + 1) * L.sc.X' := by
    rw [hXeq]
    nlinarith [mul_nonneg (add_nonneg (add_nonneg hx0.le hnpos.le) zero_le_one) (sub_nonneg.mpr hX'1)]
  have hpos : 0 < L.sc.X'' D.R.n + 1 := by
    rw [hXeq]
    have := mul_pos (mul_pos hx0 hnpos) hX'0
    linarith
  have hx1' : (0 : ℝ) < L.sc.x + 1 := by linarith
  have hn1' : (0 : ℝ) < (D.R.n : ℝ) + 1 := by linarith
  have hlog : Real.log (L.sc.X'' D.R.n + 1) ≤
      Real.log (L.sc.x + 1) + Real.log ((D.R.n : ℝ) + 1) + L.sc.x ^ (L.sc.eps / 3) := by
    calc Real.log (L.sc.X'' D.R.n + 1)
        ≤ Real.log ((L.sc.x + 1) * ((D.R.n : ℝ) + 1) * L.sc.X') := Real.log_le_log hpos hbound
      _ = Real.log (L.sc.x + 1) + Real.log ((D.R.n : ℝ) + 1) + L.sc.x ^ (L.sc.eps / 3) := by
        rw [Real.log_mul (mul_pos hx1' hn1').ne' hX'0.ne', Real.log_mul hx1'.ne' hn1'.ne']
        simp only [Scale.X', Real.log_exp]
  have h1 : Real.log (L.sc.x + 1) ≤ L.sc.x := by
    linarith [Real.log_le_sub_one_of_pos hx1']
  have h2 : Real.log ((D.R.n : ℝ) + 1) ≤ D.R.n := by
    linarith [Real.log_le_sub_one_of_pos hn1']
  have h3 : L.sc.x ^ (L.sc.eps / 3) ≤ L.sc.x ^ L.sc.eps :=
    Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith)
  have h4 : L.sc.x ≤ D.R.k := by
    have h41 : L.sc.x ^ (1 : ℝ) ≤ L.sc.x ^ (9 / 2 + 10 * L.sc.eps - Formalism.MainNotions.szTh L) :=
      Real.rpow_le_rpow_of_exponent_le hx1.le (by simp only [Formalism.MainNotions.szTh]; linarith)
    rw [Real.rpow_one] at h41
    linarith
  have h5 : (D.R.n : ℝ) ≤ D.R.k := by
    have h51 : L.sc.x ^ (2 + 8 * L.sc.eps + Formalism.MainNotions.szTh L) ≤
        L.sc.x ^ (9 / 2 + 10 * L.sc.eps - Formalism.MainNotions.szTh L) :=
      Real.rpow_le_rpow_of_exponent_le hx1.le (by simp only [Formalism.MainNotions.szTh]; linarith)
    linarith
  have hL0 : 0 ≤ L.sc.x ^ L.sc.eps := Real.rpow_nonneg hx0.le _
  have hLeq : L.sc.L = L.sc.x ^ L.sc.eps := rfl
  unfold Formalism.MainNotions.DIV.Proofs.szPol
  rw [hLeq]
  have hf : (0 : ℝ) ≤ (D.R.f : ℝ) := by positivity
  have hm : (0 : ℝ) ≤ (D.R.m : ℝ) := by positivity
  have ht : (0 : ℝ) ≤ (D.R.t : ℝ) := by positivity
  have hNm : (0 : ℝ) ≤ (D.R.N D.R.m : ℝ) := by positivity
  linarith




end Formalism.MainNotions.DIV.HookProducts.Row4

end
