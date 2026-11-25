module

public import Mathlib
public import Init.Core
public import Init.Data.Function
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Order.Lemmas
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Init.Tactics
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Linear
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
public import Mathlib.MeasureTheory.OuterMeasure.AE
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.Basic
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Order.Interval.Set.UnorderedInterval
public import Mathlib.Order.Lattice
public import Mathlib.Order.RelClasses
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.EMetricSpace.Defs
public import Mathlib.Topology.MetricSpace.Algebra
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Metrizable.Uniformity
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open MeasureTheory

namespace GlobalTheory.CompanionTheory.OneParamFourier

variable {A : Type} [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [MeasurableSpace A] [BorelSpace A]

theorem integral_translate_mul_char (lam : Measure A) [lam.IsAddHaarMeasure] (H : A → ℂ)
    (χ : AddChar A ℂ) (a : A) :
    ∫ b, H (b + a) * χ b ∂lam = χ (-a) * ∫ b, H b * χ b ∂lam := by
  have h := integral_add_right_eq_self (μ := lam) (fun b => H b * χ (b + -a)) a
  simp only [add_neg_cancel_right] at h
  rw [h, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun b => ?_)
  simp only [AddChar.map_add_eq_mul]
  ring

theorem integrable_mul_char {lam : Measure A} {H : A → ℂ} (hH : Integrable H lam)
    {χ : AddChar A ℂ} (hχ : Continuous χ) (hn : ∀ x, ‖χ x‖ = 1) :
    Integrable (fun b => H b * χ b) lam := by
  refine hH.mono (hH.aestronglyMeasurable.mul hχ.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun b => ?_)
  simp [hn]

theorem integrable_uncurry_translate (lam : Measure A) [lam.IsAddHaarMeasure] [SFinite lam]
    (c : ℝ →+ A) (hc : Continuous c) {G : A → ℂ} (hG : Continuous G) (hGi : Integrable G lam)
    {χ : AddChar A ℂ} (hχ : Continuous χ) (hn : ∀ x, ‖χ x‖ = 1) (K : ℂ) (s : ℝ) :
    Integrable (Function.uncurry fun (u : ℝ) (b : A) => K * G (b + c u) * χ b)
      ((volume.restrict (Set.uIoc 0 s)).prod lam) := by
  have hcont : Continuous (Function.uncurry fun (u : ℝ) (b : A) => K * G (b + c u) * χ b) := by
    unfold Function.uncurry
    fun_prop
  haveI : IsFiniteMeasure (volume.restrict (Set.uIoc (0 : ℝ) s)) := by
    unfold Set.uIoc
    infer_instance
  refine (integrable_prod_iff hcont.aestronglyMeasurable).2 ⟨ae_of_all _ fun u => ?_, ?_⟩
  · have h1 : Integrable (fun b => G (b + c u)) lam := hGi.comp_add_right (c u)
    have h2 := integrable_mul_char (h1.const_mul K) hχ hn
    simpa [Function.uncurry, mul_assoc] using h2
  · have hconst : ∀ u : ℝ, ∫ b, ‖Function.uncurry (fun (u : ℝ) (b : A) => K * G (b + c u) * χ b) (u, b)‖ ∂lam
        = ‖K‖ * ∫ b, ‖G b‖ ∂lam := by
      intro u
      have h := integral_add_right_eq_self (μ := lam) (fun b => ‖G b‖) (c u)
      rw [← h, ← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun b => ?_)
      simp [Function.uncurry, hn]
    simp_rw [hconst]
    exact integrable_const _

theorem integral_mul_char_eq_of_hasDerivAt (A : Type) [AddCommGroup A] [TopologicalSpace A]
    [IsTopologicalAddGroup A] [MeasurableSpace A] [BorelSpace A] (lam : Measure A)
    [lam.IsAddHaarMeasure] [SFinite lam] (c : ℝ →+ A) (hc : Continuous c) (F G : A → ℂ)
    (hF : Continuous F) (hG : Continuous G) (hFi : Integrable F lam) (hGi : Integrable G lam)
    (χ : AddChar A ℂ) (hχ : Continuous χ) (hn : ∀ x, ‖χ x‖ = 1) (f : ℝ)
    (hf : ∀ s : ℝ, χ (c s) = Complex.exp (-(2 * Real.pi * Complex.I * ((s * f : ℝ) : ℂ))))
    (hd : ∀ (b : A) (s : ℝ),
      HasDerivAt (fun t : ℝ => F (b + c t)) (2 * Real.pi * Complex.I * G (b + c s)) s) :
    ∫ b, G b * χ b ∂lam = (f : ℂ) * ∫ b, F b * χ b ∂lam := by
  set K : ℂ := 2 * Real.pi * Complex.I with hK
  have hK0 : K ≠ 0 := by
    simp [hK, Real.pi_ne_zero, Complex.I_ne_zero]
  set e : ℝ → ℂ := fun u => Complex.exp (K * ((u * f : ℝ) : ℂ)) with he
  have hχe : ∀ s : ℝ, χ (-(c s)) = e s := by
    intro s
    rw [← map_neg, hf, he]
    simp only
    congr 1
    push_cast
    ring
  set Fh : ℂ := ∫ b, F b * χ b ∂lam with hFh
  set Gh : ℂ := ∫ b, G b * χ b ∂lam with hGh
  have hec : Continuous e := by
    rw [he]
    fun_prop
  have key : ∀ s : ℝ, (e s - 1) * Fh = K * Gh * ∫ u in (0 : ℝ)..s, e u := by
    intro s
    have hftc : ∀ b : A, F (b + c s) - F b = ∫ u in (0 : ℝ)..s, K * G (b + c u) := by
      intro b
      have hcu : Continuous fun u : ℝ => K * G (b + c u) := by fun_prop
      have := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := s)
        (f := fun t : ℝ => F (b + c t)) (f' := fun u => K * G (b + c u))
        (fun x _ => hd b x) (hcu.intervalIntegrable _ _)
      simpa using this.symm
    have hswap := intervalIntegral_integral_swap
      (integrable_uncurry_translate lam c hc hG hGi hχ hn K s)
    have h1 : ∫ b, F (b + c s) * χ b ∂lam = e s * Fh := by
      rw [integral_translate_mul_char, hχe]
    have hi1 : Integrable (fun b => F (b + c s) * χ b) lam :=
      integrable_mul_char (hFi.comp_add_right (c s)) hχ hn
    have hi2 : Integrable (fun b => F b * χ b) lam := integrable_mul_char hFi hχ hn
    have h2 : (e s - 1) * Fh = ∫ b, (∫ u in (0 : ℝ)..s, K * G (b + c u) * χ b) ∂lam := by
      have : (e s - 1) * Fh = ∫ b, (F (b + c s) * χ b - F b * χ b) ∂lam := by
        rw [integral_sub hi1 hi2, h1]
        ring
      rw [this]
      refine integral_congr_ae (Filter.Eventually.of_forall fun b => ?_)
      simp only
      rw [intervalIntegral.integral_mul_const, ← hftc b]
      ring
    rw [h2, ← hswap, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun u _ => ?_
    beta_reduce
    have h3 : ∫ b, K * G (b + c u) * χ b ∂lam = K * ∫ b, G (b + c u) * χ b ∂lam := by
      rw [← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun b => ?_)
      simp only
      ring
    rw [h3, integral_translate_mul_char, hχe]
    ring
  have hL : HasDerivAt (fun s : ℝ => (e s - 1) * Fh) (K * f * Fh) 0 := by
    have h0 : HasDerivAt (fun u : ℝ => K * ((u * f : ℝ) : ℂ)) (K * f) 0 := by
      have : HasDerivAt (fun u : ℝ => ((u : ℂ))) 1 0 := Complex.ofRealCLM.hasDerivAt
      simpa [mul_assoc] using (this.mul_const (f : ℂ)).const_mul K
    have := ((h0.cexp).sub_const 1).mul_const Fh
    simpa [he] using this
  have hR : HasDerivAt (fun s : ℝ => K * Gh * ∫ u in (0 : ℝ)..s, e u) (K * Gh) 0 := by
    have := (hec.integral_hasStrictDerivAt 0 0).hasDerivAt.const_mul (K * Gh)
    simpa [he] using this
  have hEq : (fun s : ℝ => (e s - 1) * Fh) = fun s : ℝ => K * Gh * ∫ u in (0 : ℝ)..s, e u :=
    funext key
  rw [hEq] at hL
  have := hL.unique hR
  have h4 : K * (f * Fh) = K * Gh := by
    rw [← mul_assoc]
    exact this
  exact (mul_left_cancel₀ hK0 h4).symm

end GlobalTheory.CompanionTheory.OneParamFourier
