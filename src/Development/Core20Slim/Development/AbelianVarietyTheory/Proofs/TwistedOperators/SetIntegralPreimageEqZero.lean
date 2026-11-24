module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.IsApply
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Mathlib.MeasureTheory.Function.L1Space.HasFiniteIntegral
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.OuterMeasure.AE
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.Basic
public import Mathlib.Order.Notation
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.EMetricSpace.Defs
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Metrizable.Uniformity
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open MeasureTheory
open scoped NNReal ENNReal

noncomputable section

namespace GlobalTheory.FourierPush

theorem real_case {Y : Type} [MeasurableSpace Y] (m : Measure Y) (G : Y → ℝ) (hG : Integrable G m)
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] (p : Y → E) (hp : Measurable p)
    (h : ∀ l : E →L[ℝ] ℝ, ∫ y, Complex.exp ((l (p y) : ℂ) * Complex.I) * ((G y : ℝ) : ℂ) ∂m = 0)
    (s : Set E) (hs : MeasurableSet s) : ∫ y in p ⁻¹' s, G y ∂m = 0 := by
  let P := m.withDensity fun y => ENNReal.ofReal (G y)
  let P' := m.withDensity fun y => ENNReal.ofReal (-G y)
  haveI : IsFiniteMeasure P := isFiniteMeasure_withDensity_ofReal hG.2
  haveI : IsFiniteMeasure P' := isFiniteMeasure_withDensity_ofReal hG.neg.2
  have hcont : ∀ l : E →L[ℝ] ℝ, Continuous fun x : E => Complex.exp ((l x : ℂ) * Complex.I) :=
    fun l => by fun_prop
  have hbd : ∀ (l : E →L[ℝ] ℝ) (y : Y), ‖Complex.exp ((l (p y) : ℂ) * Complex.I)‖ ≤ 1 :=
    fun l y => (Complex.norm_exp_ofReal_mul_I _).le
  have hmeas : ∀ l : E →L[ℝ] ℝ,
      AEStronglyMeasurable (fun y => Complex.exp ((l (p y) : ℂ) * Complex.I)) m :=
    fun l => ((hcont l).measurable.comp hp).aestronglyMeasurable
  have e1 : ∀ l : E →L[ℝ] ℝ, charFunDual (P.map p) l
      = ∫ y, ((G y).toNNReal : ℝ) • Complex.exp ((l (p y) : ℂ) * Complex.I) ∂m := by
    intro l
    rw [charFunDual_apply, integral_map hp.aemeasurable (hcont l).aestronglyMeasurable]
    exact integral_withDensity_eq_integral_smul₀ hG.aemeasurable.real_toNNReal _
  have e2 : ∀ l : E →L[ℝ] ℝ, charFunDual (P'.map p) l
      = ∫ y, ((-G y).toNNReal : ℝ) • Complex.exp ((l (p y) : ℂ) * Complex.I) ∂m := by
    intro l
    rw [charFunDual_apply, integral_map hp.aemeasurable (hcont l).aestronglyMeasurable]
    exact integral_withDensity_eq_integral_smul₀ hG.neg.aemeasurable.real_toNNReal _
  have hmap : P.map p = P'.map p := by
    refine Measure.ext_of_charFunDual (funext fun l => ?_)
    rw [e1, e2, ← sub_eq_zero]
    have i1 : Integrable (fun y => ((G y).toNNReal : ℝ) • Complex.exp ((l (p y) : ℂ) * Complex.I)) m :=
      hG.real_toNNReal.smul_of_top_left
        (memLp_top_of_bound (hmeas l) 1 (Filter.Eventually.of_forall (hbd l)))
    have i2 : Integrable (fun y => ((-G y).toNNReal : ℝ) • Complex.exp ((l (p y) : ℂ) * Complex.I)) m :=
      hG.neg.real_toNNReal.smul_of_top_left
        (memLp_top_of_bound (hmeas l) 1 (Filter.Eventually.of_forall (hbd l)))
    rw [← integral_sub i1 i2, ← h l]
    congr 1; funext y
    rw [← sub_smul, Complex.real_smul, mul_comm]
    congr 2
    simp only [Real.coe_toNNReal']
    rcases le_total 0 (G y) with h' | h'
    · rw [max_eq_left h', max_eq_right (by linarith)]; simp
    · rw [max_eq_right h', max_eq_left (by linarith)]; simp
  have hval : ∀ f : Y → ℝ, ∫⁻ y in p ⁻¹' s, ENNReal.ofReal (f y) ∂m
      = (m.withDensity fun y => ENNReal.ofReal (f y)).map p s := fun f => by
    rw [Measure.map_apply hp hs, withDensity_apply _ (hp hs)]
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hG.integrableOn, hval G,
    hval (fun y => -G y)]
  change (P.map p s).toReal - (P'.map p s).toReal = 0
  rw [hmap, sub_self]

theorem setIntegral_preimage_eq_zero (Y : Type) [MeasurableSpace Y] (m : Measure Y) (F : Y → ℂ)
    (hF : Integrable F m) (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (p : Y → E) (hp : Measurable p)
    (h : ∀ l : E →L[ℝ] ℝ, ∫ y, Complex.exp ((l (p y) : ℂ) * Complex.I) * F y ∂m = 0)
    (s : Set E) (hs : MeasurableSet s) : ∫ y in p ⁻¹' s, F y ∂m = 0 := by
  have hcont : ∀ l : E →L[ℝ] ℝ, Continuous fun x : E => Complex.exp ((l x : ℂ) * Complex.I) :=
    fun l => by fun_prop
  have hI : ∀ l : E →L[ℝ] ℝ, Integrable (fun y => Complex.exp ((l (p y) : ℂ) * Complex.I) * F y) m :=
    fun l => hF.bdd_mul ((hcont l).measurable.comp hp).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => (Complex.norm_exp_ofReal_mul_I _).le)
  have hic : Integrable (fun y => (starRingEnd ℂ) (F y)) m := by
    refine ⟨hF.1.star, ?_⟩
    simpa [HasFiniteIntegral] using hF.2
  have hI' : ∀ l : E →L[ℝ] ℝ,
      Integrable (fun y => Complex.exp ((l (p y) : ℂ) * Complex.I) * (starRingEnd ℂ) (F y)) m :=
    fun l => hic.bdd_mul ((hcont l).measurable.comp hp).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => (Complex.norm_exp_ofReal_mul_I _).le)
  have hconj : ∀ (l : E →L[ℝ] ℝ) (x : E),
      (starRingEnd ℂ) (Complex.exp ((((-l) x : ℝ) : ℂ) * Complex.I)) = Complex.exp (((l x : ℝ) : ℂ) * Complex.I) := by
    intro l x
    rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
    congr 1
    simp
  have hc' : ∀ l : E →L[ℝ] ℝ, ∫ y, Complex.exp ((l (p y) : ℂ) * Complex.I) * (starRingEnd ℂ) (F y) ∂m = 0 := by
    intro l
    have := congrArg (starRingEnd ℂ) (h (-l))
    rw [← integral_conj, map_zero] at this
    simpa only [map_mul, hconj] using this
  have hre : ∀ l : E →L[ℝ] ℝ,
      ∫ y, Complex.exp ((l (p y) : ℂ) * Complex.I) * (((F y).re : ℝ) : ℂ) ∂m = 0 := fun l => by
    simp only [Complex.re_eq_add_conj, mul_div_assoc', mul_add]
    rw [integral_div, integral_add (hI l) (hI' l), h l, hc' l]; simp
  have him : ∀ l : E →L[ℝ] ℝ,
      ∫ y, Complex.exp ((l (p y) : ℂ) * Complex.I) * (((F y).im : ℝ) : ℂ) ∂m = 0 := fun l => by
    simp only [Complex.im_eq_sub_conj, mul_div_assoc', mul_sub]
    rw [integral_div, integral_sub (hI l) (hI' l), h l, hc' l]; simp
  have h1 := real_case m (fun y => (F y).re) hF.re p hp hre s hs
  have h2 := real_case m (fun y => (F y).im) hF.im p hp him s hs
  apply Complex.ext
  · rw [Complex.zero_re, ← h1]
    exact (integral_re hF.integrableOn).symm
  · rw [Complex.zero_im, ← h2]
    exact (integral_im hF.integrableOn).symm

end GlobalTheory.FourierPush

end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open   GlobalTheory.Grow    
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
