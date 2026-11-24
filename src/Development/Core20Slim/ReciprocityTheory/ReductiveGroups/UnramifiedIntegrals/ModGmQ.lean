module

public import Mathlib
public import Development.Core20Slim.ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModDefs
public import Development.Core20Slim.ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModBasic
public import Development.Core20Slim.ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.CoeffRescaleExpandOfNotDvd
public import Development.Core20Slim.ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModEvalSer
public import Development.Core20Slim.ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModEvalMF
public import Development.Core20Slim.ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModFacSer
public import Development.Core20Slim.ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModGmForm
public import Batteries.Logic
public import Init.ByCases
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Int.Order
public import Init.Data.Nat.Basic
public import Init.Data.Nat.Div.Basic
public import Init.Data.Nat.Dvd
public import Init.Data.NeZero
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Divisibility.Basic
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Even
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.Group.Defs
public import Mathlib.Algebra.Order.Group.Int
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Ring.Unbundled.Basic
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Algebra.Order.Star.Int
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Ring.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.Real.Star
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Empty
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Finset.Range
public import Mathlib.Data.Finset.Sigma
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Cast.Order.Basic
public import Mathlib.Data.Nat.Init
public import Mathlib.Logic.Function.Defs
public import Mathlib.NumberTheory.Divisors
public import Mathlib.NumberTheory.ModularForms.QExpansion
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.RelClasses
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.Tactic.FieldSimp.Lemmas
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Positivity.Core
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Tactic.Zify
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.SummationFilter
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM

namespace ReciprocityTheory.ChartRestriction.L1

theorem prodSer_coeffIn {m : ℕ} (hm : 0 < m) : CoeffIn (Rm m) (prodSer m) := by
  unfold prodSer
  refine Finset.prod_induction _ (CoeffIn (Rm m)) (fun a b ha hb => ha.mul hb) ?_
    (fun t ht => facSer_coeffIn hm ht)
  intro n
  rw [PowerSeries.coeff_one]
  split_ifs
  · exact Subring.one_mem _
  · exact Subring.zero_mem _

theorem prodSer_conv {m : ℕ} (hm : 0 < m) : Conv (prodSer m) := by
  unfold prodSer
  refine Finset.prod_induction _ Conv (fun a b ha hb => ha.mul hb) ?_
    (fun t ht => facSer_conv hm ht)
  intro x _
  refine (hasSum_single 0 fun n hn => ?_).summable
  simp [PowerSeries.coeff_one, hn]

theorem prodSer_ev {m : ℕ} (hm : 0 < m) (τ : ℍ) : ev (prodSer m) (qm m τ) = Gm m τ := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hx : ‖qm m τ‖ < 1 := by
    unfold qm
    rw [Complex.norm_exp]
    have e : (2 * (Real.pi : ℂ) * Complex.I * (τ : ℂ) / (m : ℂ)).re = -(2 * Real.pi * τ.im) / m := by
      rw [Complex.div_natCast_re]
      simp
    rw [e, ← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (div_neg_of_neg_of_pos (by nlinarith [Real.pi_pos, τ.im_pos]) hm')
  have h1 : Conv (1 : PowerSeries ℂ) := by
    intro x _
    refine (hasSum_single 0 fun n hn => ?_).summable
    simp [PowerSeries.coeff_one, hn]
  have key : ∀ s ⊆ Tm m, Conv (∏ t ∈ s, facSer m t) ∧
      ev (∏ t ∈ s, facSer m t) (qm m τ) = ∏ t ∈ s, fac t τ := by
    intro s
    classical
    refine Finset.induction_on s ?_ ?_
    · intro _
      refine ⟨by simpa using h1, ?_⟩
      simp only [Finset.prod_empty]
      unfold ev
      rw [tsum_eq_single 0 fun n hn => by simp [PowerSeries.coeff_one, hn]]
      simp
    · intro a s ha ih hs
      have has : a ∈ Tm m := hs (Finset.mem_insert_self a s)
      obtain ⟨c1, c2⟩ := ih fun y hy => hs (Finset.mem_insert_of_mem hy)
      rw [Finset.prod_insert ha, Finset.prod_insert ha]
      exact ⟨(facSer_conv hm has).mul c1, by
        rw [ev_mul (facSer_conv hm has) c1 hx, facSer_ev hm has, c2]⟩
  unfold prodSer Gm
  exact (key _ subset_rfl).2

theorem prodSer_low {m : ℕ} (hm : 0 < m) (hsq : ¬ IsSquare m) : ∃ n0 u, LowUnit (Rm m) (prodSer m) n0 u := by
  unfold prodSer
  refine LowUnit.prod _ _ fun t ht => facSer_low hm ht ?_
  intro heq
  apply hsq
  unfold Tm at ht
  rw [Finset.mem_image] at ht
  obtain ⟨x, hx, rfl⟩ := ht
  rw [Finset.mem_sigma, Nat.mem_divisors] at hx
  dsimp only at heq
  refine ⟨x.1, ?_⟩
  have h2 := Nat.div_mul_cancel hx.1.1
  rw [← heq] at h2
  exact h2.symm

theorem gmQ_xp {m : ℕ} (hm : 0 < m) : xp m (qExpansion 1 (Gm m)) = prodSer m := by
  have hm0 : m ≠ 0 := hm.ne'
  have hF := gmForm hm
  refine eq_of_ev_eq (hF.conv.xp hm0) (prodSer_conv hm) ?_
  intro x hx0 hx1
  rw [ev_xp _ hm0]
  have hxne : x ≠ 0 := norm_pos_iff.mp hx0
  have hmR : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm0
  have hmC : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm0
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hlog : Real.log ‖x‖ < 0 := Real.log_neg hx0 hx1

  let w : ℂ := ⟨(m : ℝ) * Complex.arg x / (2 * Real.pi), -((m : ℝ) * Real.log ‖x‖) / (2 * Real.pi)⟩
  have him : 0 < w.im := by
    show 0 < -((m : ℝ) * Real.log ‖x‖) / (2 * Real.pi)
    apply div_pos _ (by positivity)
    nlinarith
  let τ : ℍ := ⟨w, him⟩
  have hτ : (τ : ℂ) = w := rfl
  have hlogx : 2 * (Real.pi : ℂ) * Complex.I * w / (m : ℂ) = Complex.log x := by
    apply Complex.ext
    · rw [Complex.div_natCast_re, Complex.log_re]
      simp [w]
      field_simp
    · rw [Complex.div_natCast_im, Complex.log_im]
      simp [w]
      field_simp
  have hq : qm m τ = x := by
    unfold qm
    rw [hτ, hlogx, Complex.exp_log hxne]
  have hq1 : qm 1 τ = x ^ m := by
    rw [← hq]
    unfold qm
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    field_simp
  rw [← hq1, hF.ev_eq τ, ← prodSer_ev hm τ, hq]

theorem gmQ_coeffIn {m : ℕ} (hm : 0 < m) : CoeffIn (Rm m) (qExpansion 1 (Gm m)) := by
  intro n
  have h := congrArg (PowerSeries.coeff (m * n)) (gmQ_xp hm)
  simp only [xp, PowerSeries.coeff_mk, dvd_mul_right, if_true, Nat.mul_div_cancel_left n hm] at h
  rw [h]
  exact prodSer_coeffIn hm (m * n)

theorem gmQ_low {m : ℕ} (hm : 0 < m) (hsq : ¬ IsSquare m) :
    ∃ n0 u, LowUnit (Rm m) (qExpansion 1 (Gm m)) n0 u := by
  obtain ⟨n0, u, hu1, hu2, hu3, hlow, hn0⟩ := prodSer_low hm hsq
  have hc : ∀ n, PowerSeries.coeff n (prodSer m) =
      if m ∣ n then PowerSeries.coeff (n / m) (qExpansion 1 (Gm m)) else 0 := by
    intro n
    rw [← gmQ_xp hm]
    simp [xp]
  have hdvd : m ∣ n0 := by
    by_contra h
    rw [hc, if_neg h] at hn0
    exact hu3 hn0.symm
  obtain ⟨k, rfl⟩ := hdvd
  refine ⟨k, u, hu1, hu2, hu3, fun j hj => ?_, ?_⟩
  · have h2 := hlow (m * j) (by nlinarith)
    rw [hc, if_pos (dvd_mul_right m j), Nat.mul_div_cancel_left j hm] at h2
    exact h2
  · rw [hc, if_pos (dvd_mul_right m k), Nat.mul_div_cancel_left k hm] at hn0
    exact hn0

end ReciprocityTheory.ChartRestriction.L1
