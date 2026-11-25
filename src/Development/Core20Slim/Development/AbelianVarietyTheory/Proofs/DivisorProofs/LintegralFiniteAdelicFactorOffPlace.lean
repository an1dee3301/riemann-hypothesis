module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActFromBlocks
public import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarAdelicVectorsBoundsPureTensorsSlices
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MeasurableEmbeddingAdelicTupleLocalComponents
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RestrictedProductIntegralPureTensorEqProd
public import Formalism.LocalToGlobal.IndefiniteReal.PHeisFCA
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Classical
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.WithOne.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Notation.Indicator
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Countable.Defs
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Lattice.Indexed
public import Mathlib.Data.Set.Operations
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Mathlib.MeasureTheory.Group.Arithmetic
public import Mathlib.MeasureTheory.Group.Defs
public import Mathlib.MeasureTheory.Group.LIntegral
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.Order.SetNotation
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.Group.ContinuousInv
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.Nonarchimedean.Basic
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Valued.NormedValued
public import Mathlib.Topology.Algebra.Valued.ValuationTopology
public import Mathlib.Topology.Algebra.Valued.ValuedField
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Basic
public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.Compactness.SigmaCompact
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.EMetricSpace.Defs
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.UniformSpace.Cauchy
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open scoped Matrix GlobalTheory.VacAny ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RatWeilOp

namespace GlobalTheory.HaarFactorOffPlace

theorem lintegral_factor {A V : Type} [AddCommGroup A] [MeasurableSpace A] [MeasurableAdd₂ A]
    [MeasurableNeg A] [AddCommGroup V] [MeasurableSpace V] [MeasurableAdd₂ V] [MeasurableNeg V]
    (μ : Measure A) (ν : Measure V) [SFinite μ] [SFinite ν] [μ.IsAddRightInvariant]
    [ν.IsAddRightInvariant] (c : A → V) (e : V → A) (hcm : Measurable c)
    (hce : ∀ y t, c (y + e t) = c y + t) (O : Set V) (hOm : MeasurableSet O)
    (hOneg : ∀ x, x ∈ O ↔ -x ∈ O) (hO : ν O = 1) (K : A → ℝ≥0∞) (hK : Measurable K)
    (hKe : ∀ y t, K (y + e t) = K y) (g : V → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ y, g (c y) * K y ∂μ = (∫⁻ t, g t ∂ν) * ∫⁻ y, O.indicator 1 (c y) * K y ∂μ := by
  have hχm : Measurable (O.indicator (1 : V → ℝ≥0∞)) := measurable_one.indicator hOm
  have hcs : ∀ y t, c (y - e t) = c y - t := fun y t => by
    have h := hce (y - e t) t
    rw [sub_add_cancel] at h
    rw [h, add_sub_cancel_right]
  have hKs : ∀ y t, K (y - e t) = K y := fun y t => by
    have h := hKe (y - e t) t
    rw [sub_add_cancel] at h
    exact h.symm
  have hχneg : ∀ x, O.indicator (1 : V → ℝ≥0∞) (-x) = O.indicator 1 x := fun x => by
    by_cases hx : x ∈ O
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem ((hOneg x).1 hx)]; rfl
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun h => hx ((hOneg x).2 h))]
  have hχint : ∫⁻ t, O.indicator 1 t ∂ν = 1 := by
    rw [lintegral_indicator_one hOm]; exact hO
  have hA : ∀ t, ∫⁻ y, g (c y) * K y ∂μ = ∫⁻ y, g (c y + t) * K y ∂μ := fun t => by
    rw [← lintegral_add_right_eq_self (fun y => g (c y) * K y) (e t)]
    simp only [hce, hKe]
  have hL : ∫⁻ y, g (c y) * K y ∂μ =
      ∫⁻ y, ∫⁻ s, O.indicator 1 (s - c y) * (g s * K y) ∂ν ∂μ := by
    calc ∫⁻ y, g (c y) * K y ∂μ
        = (∫⁻ t, O.indicator 1 t ∂ν) * ∫⁻ y, g (c y) * K y ∂μ := by rw [hχint, one_mul]
      _ = ∫⁻ t, O.indicator 1 t * ∫⁻ y, g (c y) * K y ∂μ ∂ν := (lintegral_mul_const _ hχm).symm
      _ = ∫⁻ t, O.indicator 1 t * ∫⁻ y, g (c y + t) * K y ∂μ ∂ν :=
          lintegral_congr fun t => by rw [← hA t]
      _ = ∫⁻ t, ∫⁻ y, O.indicator 1 t * (g (c y + t) * K y) ∂μ ∂ν :=
          lintegral_congr fun t =>
            (lintegral_const_mul _ ((hg.comp (hcm.add_const t)).mul hK)).symm
      _ = ∫⁻ y, ∫⁻ t, O.indicator 1 t * (g (c y + t) * K y) ∂ν ∂μ := by
          apply lintegral_lintegral_swap
          exact ((hχm.comp measurable_fst).mul
            ((hg.comp ((hcm.comp measurable_snd).add measurable_fst)).mul
              (hK.comp measurable_snd))).aemeasurable
      _ = ∫⁻ y, ∫⁻ s, O.indicator 1 (s - c y) * (g s * K y) ∂ν ∂μ := by
          refine lintegral_congr fun y => ?_
          rw [← lintegral_sub_right_eq_self (fun t => O.indicator 1 t * (g (c y + t) * K y)) (c y)]
          refine lintegral_congr fun s => ?_
          simp only [add_sub_cancel]
  have hM : ∀ s, ∫⁻ y, O.indicator 1 (c y) * K y ∂μ =
      ∫⁻ y, O.indicator 1 (s - c y) * K y ∂μ := fun s => by
    rw [← lintegral_sub_right_eq_self (fun y => O.indicator 1 (c y) * K y) (e s)]
    refine lintegral_congr fun y => ?_
    simp only [hcs, hKs]
    rw [← neg_sub, hχneg]
  rw [hL]
  calc ∫⁻ y, ∫⁻ s, O.indicator 1 (s - c y) * (g s * K y) ∂ν ∂μ
      = ∫⁻ s, ∫⁻ y, O.indicator 1 (s - c y) * (g s * K y) ∂μ ∂ν := by
        apply lintegral_lintegral_swap
        exact ((hχm.comp (measurable_snd.sub (hcm.comp measurable_fst))).mul
          ((hg.comp measurable_snd).mul (hK.comp measurable_fst))).aemeasurable
    _ = ∫⁻ s, g s * ∫⁻ y, O.indicator 1 (s - c y) * K y ∂μ ∂ν := by
        refine lintegral_congr fun s => ?_
        have hm : Measurable fun y => O.indicator (1 : V → ℝ≥0∞) (s - c y) * K y :=
          (hχm.comp (measurable_const.sub hcm)).mul hK
        rw [← lintegral_const_mul _ hm]
        refine lintegral_congr fun y => ?_
        ring
    _ = ∫⁻ s, g s * ∫⁻ y, O.indicator 1 (c y) * K y ∂μ ∂ν :=
        lintegral_congr fun s => by rw [← hM s]
    _ = (∫⁻ t, g t ∂ν) * ∫⁻ y, O.indicator 1 (c y) * K y ∂μ := lintegral_mul_const _ hg

end GlobalTheory.HaarFactorOffPlace

namespace GlobalTheory.HaarFactorOffPlace

theorem lintegral_evalV_mul_shiftInvariant : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] [MeasurableSpace (κ → Af F)] [BorelSpace (κ → Af F)]
    (w : HeightOneSpectrum (𝓞 F)) [MeasurableSpace (κ → Fv F w)] [BorelSpace (κ → Fv F w)]
    (μf : Measure (κ → Af F)) [μf.IsAddHaarMeasure] (μw : Measure (κ → Fv F w)) [μw.IsAddHaarMeasure],
    μw {t | ∀ i, t i ∈ w.adicCompletionIntegers F} = 1 →
    ∀ (K : (κ → Af F) → ℝ≥0∞), Measurable K → (∀ (y : κ → Af F) (t : κ → Fv F w), K (fun i => y i + singleFin w (t i)) = K y) →
    ∀ (g : (κ → Fv F w) → ℝ≥0∞), Measurable g →
      ∫⁻ y, g (fun i => evalV F w (y i)) * K y ∂μf =
        (∫⁻ t, g t ∂μw) * ∫⁻ y, {t : κ → Fv F w | ∀ i, t i ∈ w.adicCompletionIntegers F}.indicator 1 (fun i => evalV F w (y i)) * K y ∂μf := by
  intro F _ _ κ _ _ _ w _ _ μf _ μw _ hO K hK hKinv g hg
  haveI := GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion F w
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele F
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele F
  haveI : SecondCountableTopology (κ → Af F) := inferInstance
  haveI : SecondCountableTopology (κ → Fv F w) := inferInstance
  haveI : LocallyCompactSpace (κ → Af F) := inferInstance
  haveI : LocallyCompactSpace (κ → Fv F w) := inferInstance
  have hcont : Continuous fun (y : κ → Af F) (i : κ) => evalV F w (y i) :=
    continuous_pi fun i => (GlobalTheory.GaugeGlue.continuous_evalV w).comp (continuous_apply i)
  have hOc : IsClosed {t : κ → Fv F w | ∀ i, t i ∈ w.adicCompletionIntegers F} := by
    simp only [Set.setOf_forall]
    exact isClosed_iInter fun i =>
      (Valued.isClosed_integer (Fv F w)).preimage (continuous_apply i)
  refine lintegral_factor μf μw (fun y i => evalV F w (y i)) (fun t i => singleFin w (t i))
    hcont.measurable ?_ _ hOc.measurableSet ?_ hO K hK (fun y t => hKinv y t) g hg
  · intro y t
    funext i
    simp only [Pi.add_apply, map_add (f := _), evalV_singleFin_self]
  · intro x
    simp only [Set.mem_setOf_eq, Pi.neg_apply, neg_mem_iff]

end GlobalTheory.HaarFactorOffPlace
