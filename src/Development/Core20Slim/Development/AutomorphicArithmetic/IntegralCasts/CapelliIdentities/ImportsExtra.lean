module

public import Mathlib
public import Batteries.Logic
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Module.Defs
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
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Order.Lattice
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.ENNReal.Real
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.Real.Star
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Cast.Order.Basic
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.BooleanAlgebra
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Logic.Function.Defs
public import Mathlib.Logic.Pairwise
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.MeasureTheory.OuterMeasure.AE
public import Mathlib.Order.Basic
public import Mathlib.Order.CompleteBooleanAlgebra
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Disjoint
public import Mathlib.Order.Filter.Basic
public import Mathlib.Order.Notation
public import Mathlib.Order.SetNotation
public import Mathlib.Tactic.CancelDenoms.Core
public import Mathlib.Tactic.FieldSimp.Lemmas
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.Linarith.Preprocessing
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Positivity.Core
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Order.OrderClosed
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

theorem UpperTheory.Reformulated.B.DYga2.main.{u_1} :
    ∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E]
      [inst_3 : MeasurableSpace E] [BorelSpace E] (μ : MeasureTheory.Measure E) [μ.IsAddHaarMeasure] {A : ℕ},
      Module.finrank ℝ E < A →
        (0 : ℕ) < Module.finrank ℝ E →
          ∃ (c : ℝ),
            (0 : ℝ) ≤ c ∧
              ∀ (η : ℝ),
                (0 : ℝ) < η →
                  ∀ (F : Finset E),
                    (∀ y ∈ F, ∀ y' ∈ F, y ≠ y' → η ≤ ‖y - y'‖ ^ Module.finrank ℝ E) →
                      ∑ y ∈ F, (((1 : ℝ) + ‖y‖) ^ A)⁻¹ ≤ c * ((1 : ℝ) + η⁻¹) := by
  intro E _ _ _ _ _ μ _ A hA hd
  set d := Module.finrank ℝ E with hd_def

  set w : E → ℝ := fun x => ((1 + ‖x‖) ^ A)⁻¹ with hw
  have hwpos : ∀ x, 0 < w x := fun x => by
    have : (0:ℝ) < 1 + ‖x‖ := by positivity
    simp only [hw]; positivity
  have hint : MeasureTheory.Integrable w μ := by
    have h := integrable_one_add_norm (E := E) (μ := μ) (r := (A:ℝ)) (by exact_mod_cast hA)
    refine h.congr (Filter.Eventually.of_forall fun x => ?_)
    have : (0:ℝ) < 1 + ‖x‖ := by positivity
    simp only [hw]
    rw [Real.rpow_neg this.le, Real.rpow_natCast]
  set I : ℝ := ∫ x, w x ∂μ with hI
  have hI0 : 0 ≤ I := MeasureTheory.integral_nonneg fun x => (hwpos x).le
  set V : ℝ := μ.real (Metric.ball (0:E) 1) with hV
  have hVpos : 0 < V := by
    refine ENNReal.toReal_pos ?_ ?_
    · exact (Metric.measure_ball_pos μ 0 one_pos).ne'
    · exact MeasureTheory.measure_ball_lt_top.ne
  refine ⟨2 ^ A * I / V * 2 ^ d, by positivity, ?_⟩
  intro η hη F hF
  have hdR : (d:ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  set r : ℝ := η ^ ((d:ℝ)⁻¹) with hr
  have hrpos : 0 < r := Real.rpow_pos_of_pos hη _
  have hrd : r ^ d = η := by
    rw [hr, ← Real.rpow_natCast, ← Real.rpow_mul hη.le, inv_mul_cancel₀ hdR, Real.rpow_one]
  set s : ℝ := min (r / 2) 1 with hs
  have hspos : 0 < s := lt_min (by positivity) one_pos
  have hs1 : s ≤ 1 := min_le_right _ _
  have hs2 : 2 * s ≤ r := by
    have : s ≤ r / 2 := min_le_left _ _
    linarith

  have hkey : 1 ≤ s ^ d * (2 ^ d * (1 + η⁻¹)) := by
    have hη' : 0 < η⁻¹ := inv_pos.mpr hη
    rcases le_total (r / 2) 1 with h | h
    · have : s = r / 2 := min_eq_left h
      rw [this, div_pow, hrd]
      have h2 : (2:ℝ) ^ d ≠ 0 := by positivity
      have : η / 2 ^ d * (2 ^ d * (1 + η⁻¹)) = η + 1 := by
        field_simp
      rw [this]; linarith
    · have : s = 1 := min_eq_right h
      rw [this, one_pow, one_mul]
      have : (1:ℝ) ≤ 2 ^ d := one_le_pow₀ (by norm_num)
      nlinarith

  have hball : ∀ y : E, μ.real (Metric.ball y s) = s ^ d * V := by
    intro y
    have := MeasureTheory.Measure.addHaar_ball_of_pos μ y hspos
    simp only [MeasureTheory.Measure.real, hV]
    rw [this, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]

  have hcomp : ∀ y x : E, x ∈ Metric.ball y s → (2 ^ A)⁻¹ * w y ≤ w x := by
    intro y x hx
    have hxy : ‖x‖ ≤ ‖y‖ + s := by
      have h1 : ‖x - y‖ < s := by simpa [dist_eq_norm] using hx
      have h2 : ‖x‖ ≤ ‖y‖ + ‖x - y‖ := by
        have := norm_add_le y (x - y)
        simpa using this
      linarith
    have hle : 1 + ‖x‖ ≤ 2 * (1 + ‖y‖) := by
      have := norm_nonneg y
      linarith
    have hx0 : (0:ℝ) < 1 + ‖x‖ := by positivity
    have hy0 : (0:ℝ) < 1 + ‖y‖ := by positivity
    have hp : (1 + ‖x‖) ^ A ≤ 2 ^ A * (1 + ‖y‖) ^ A := by
      rw [← mul_pow]; exact pow_le_pow_left₀ hx0.le hle A
    simp only [hw]
    rw [← mul_inv]
    exact inv_anti₀ (by positivity) hp

  have hone : ∀ y : E, (2 ^ A)⁻¹ * w y * (s ^ d * V) ≤ ∫ x in Metric.ball y s, w x ∂μ := by
    intro y
    have := MeasureTheory.setIntegral_ge_of_const_le_real (μ := μ) (f := w) (c := (2 ^ A)⁻¹ * w y)
      (s := Metric.ball y s) Metric.isOpen_ball.measurableSet MeasureTheory.measure_ball_lt_top.ne
      (fun x hx => hcomp y x hx) hint.integrableOn
    rw [hball] at this
    exact this

  have hdisj : Set.Pairwise (F : Set E) (Function.onFun Disjoint fun y => Metric.ball y s) := by
    intro y hy y' hy' hne
    refine Metric.ball_disjoint_ball ?_
    have h1 := hF y hy y' hy' hne
    have h2 : r ≤ ‖y - y'‖ := by
      rw [← hrd] at h1
      exact le_of_pow_le_pow_left₀ hd.ne' (norm_nonneg _) h1
    rw [dist_eq_norm]
    linarith
  have hsum : ∑ y ∈ F, ∫ x in Metric.ball y s, w x ∂μ ≤ I := by
    rw [← MeasureTheory.integral_biUnion_finset F (fun y _ => Metric.isOpen_ball.measurableSet) hdisj
      (fun y _ => hint.integrableOn)]
    exact MeasureTheory.setIntegral_le_integral hint
      (Filter.Eventually.of_forall fun x => (hwpos x).le)
  have htot : (2 ^ A)⁻¹ * (s ^ d * V) * ∑ y ∈ F, w y ≤ I := by
    refine le_trans ?_ hsum
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun y _ => ?_
    calc _ = (2 ^ A)⁻¹ * w y * (s ^ d * V) := by ring
      _ ≤ _ := hone y
  have hS0 : 0 ≤ ∑ y ∈ F, w y := Finset.sum_nonneg fun y _ => (hwpos y).le
  have hsd : 0 < s ^ d := by positivity
  have hfin : ∑ y ∈ F, w y ≤ 2 ^ A * I / V * (1 / s ^ d) := by
    have h2 : (0:ℝ) < 2 ^ A := by positivity
    rw [show 2 ^ A * I / V * (1 / s ^ d) = (2 ^ A * I) / (s ^ d * V) by field_simp]
    rw [le_div_iff₀ (by positivity)]
    have := mul_le_mul_of_nonneg_left htot h2.le
    calc _ = 2 ^ A * ((2 ^ A)⁻¹ * (s ^ d * V) * ∑ y ∈ F, w y) := by field_simp
      _ ≤ _ := this
  have hinv : 1 / s ^ d ≤ 2 ^ d * (1 + η⁻¹) := by
    rw [div_le_iff₀ hsd]
    linarith [hkey, mul_comm (s ^ d) (2 ^ d * (1 + η⁻¹))]
  calc ∑ y ∈ F, ((1 + ‖y‖) ^ A)⁻¹ = ∑ y ∈ F, w y := rfl
    _ ≤ 2 ^ A * I / V * (1 / s ^ d) := hfin
    _ ≤ 2 ^ A * I / V * (2 ^ d * (1 + η⁻¹)) :=
        mul_le_mul_of_nonneg_left hinv (by positivity)
    _ = 2 ^ A * I / V * 2 ^ d * (1 + η⁻¹) := by ring
