module

public import Mathlib
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.DisintegrationDensityExists
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ContinuousDensitiesEqOfIntegralsOnCompactsStatement
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.DisintegrationDensityContinuous
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Classical
public import Init.Core
public import Init.Data.Function
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Notation.Indicator
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Notation.Support
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.ZeroLEOne
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Order.Lattice
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.ENNReal.Real
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Set.BooleanAlgebra
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Insert
public import Mathlib.Data.Set.Operations
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map
public import Mathlib.MeasureTheory.MeasurableSpace.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Module
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.MeasureTheory.OuterMeasure.AE
public import Mathlib.MeasureTheory.OuterMeasure.Basic
public import Mathlib.Order.Basic
public import Mathlib.Order.BoundedOrder.Basic
public import Mathlib.Order.CompleteBooleanAlgebra
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.Basic
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Lattice
public import Mathlib.Order.Notation
public import Mathlib.Topology.Algebra.Group.ContinuousDiv
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.Support
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Closure
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.ContinuousOn
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Instances.ENNReal.Lemmas
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Neighborhoods
public import Mathlib.Topology.Order.OrderClosed
public import Mathlib.Topology.Order.Real
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open MeasureTheory Topology
open scoped ENNReal NNReal

namespace GlobalTheory.CompanionTheory.SW.FibreShift

theorem comp_shift_props {V : Type} [TopologicalSpace V] [T2Space V] {W : Set V} (hW : IsOpen W)
    {T T' : V → V} (hT : ContinuousOn T W) (hT' : ContinuousOn T' W)
    (hmem : ∀ v, T v ∈ W ↔ v ∈ W) (hmem' : ∀ v, T' v ∈ W ↔ v ∈ W)
    (hinv : ∀ v ∈ W, T' (T v) = v) {φ : V → ℝ} (hφ : Continuous φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ W) :
    Continuous (fun v => φ (T v)) ∧ HasCompactSupport (fun v => φ (T v)) ∧
      tsupport (fun v => φ (T v)) ⊆ W := by
  have hC : IsCompact (T' '' tsupport φ) := hc.isCompact.image_of_continuousOn (hT'.mono hs)
  have hCW : T' '' tsupport φ ⊆ W := by
    rintro _ ⟨w, hw, rfl⟩
    exact (hmem' w).2 (hs hw)
  have hsup : ∀ v, v ∉ T' '' tsupport φ → φ (T v) = 0 := by
    intro v hv
    by_contra h
    have h1 : T v ∈ tsupport φ := subset_tsupport _ h
    exact hv ⟨T v, h1, hinv v ((hmem v).1 (hs h1))⟩
  have hts : tsupport (fun v => φ (T v)) ⊆ T' '' tsupport φ := by
    refine closure_minimal ?_ hC.isClosed
    intro v hv
    by_contra h
    exact hv (hsup v h)
  refine ⟨continuous_of_tsupport fun v hv => ?_, HasCompactSupport.intro hC hsup, hts.trans hCW⟩
  exact ContinuousAt.comp (g := φ) hφ.continuousAt (hT.continuousAt (hW.mem_nhds (hCW (hts hv))))

theorem continuous_lintegral {V X Y : Type} [TopologicalSpace V] [MeasurableSpace V]
    [TopologicalSpace X] [MeasurableSpace X] {μ : Measure V} {ν : Measure X} {f : V → Y}
    {ι : X → Y} {U : Set V} {fib : X → Measure V}
    (h : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι U ν Set.univ fib) {φ : V → ℝ}
    (hφ : Continuous φ) (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ U) (h0 : ∀ v, 0 ≤ φ v) :
    Continuous fun b => ∫⁻ v, ENNReal.ofReal (φ v) ∂(fib b) := by
  obtain ⟨hi, hc1⟩ := h.2.2 φ hφ hc hs
  have hcont : Continuous fun b => ENNReal.ofReal (∫ v, φ v ∂(fib b)) :=
    ENNReal.continuous_ofReal.comp (continuousOn_univ.1 hc1)
  exact hcont.congr fun b =>
    ofReal_integral_eq_lintegral_ofReal (hi b (Set.mem_univ b)) (Filter.Eventually.of_forall h0)

theorem setLIntegral_eq_lintegral {V : Type} [MeasurableSpace V] {μ : Measure V} {W : Set V}
    (hW : MeasurableSet W) {a : V → ℝ≥0∞} (ha : ∀ v, v ∉ W → a v = 0) :
    ∫⁻ v in W, a v ∂μ = ∫⁻ v, a v ∂μ := by
  rw [← lintegral_indicator hW]
  congr 1
  funext v
  by_cases hv : v ∈ W
  · rw [Set.indicator_of_mem hv]
  · rw [Set.indicator_of_notMem hv, ha v hv]

theorem lintegral_shift {V X Y : Type} [TopologicalSpace V] [T2Space V] [MeasurableSpace V]
    [BorelSpace V] [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
    [LocallyCompactSpace X] [SecondCountableTopology X] [T2Space X] [MeasurableSpace X]
    [BorelSpace X] {μ : Measure V} {ν : Measure X} [ν.IsAddHaarMeasure] {f : V → Y} {g : V → X}
    {ι : X → Y} (hι : Function.Injective ι) (hg : Continuous g) (hf : ∀ v, f v = ι (g v))
    {U W : Set V} (hW : IsOpen W) (hWU : W ⊆ U) {fib : X → Measure V}
    (hF : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι U ν Set.univ fib) {T : X → V → V}
    (hTm : ∀ s, Measurable (T s)) (hTμ : ∀ s, μ.map (T s) = μ)
    (hTc : ∀ s, ContinuousOn (T s) W) (hTW : ∀ s v, T s v ∈ W ↔ v ∈ W)
    (hinv : ∀ s, ∀ v ∈ W, T (-s) (T s v) = v) (hgT : ∀ s, ∀ v ∈ W, g (T s v) = g v + s)
    {φ : V → ℝ} (hφ : Continuous φ) (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ W)
    (h0 : ∀ v, 0 ≤ φ v) (s c : X) :
    ∫⁻ v, ENNReal.ofReal (φ (T s v)) ∂(fib c) = ∫⁻ v, ENNReal.ofReal (φ v) ∂(fib (c + s)) := by
  obtain ⟨hφs, hcs, hss⟩ :=
    comp_shift_props hW (hTc s) (hTc (-s)) (hTW s) (hTW (-s)) (hinv s) hφ hc hs
  have hψm : Measurable fun v => ENNReal.ofReal (φ v) :=
    ENNReal.measurable_ofReal.comp hφ.measurable
  have hψ0 : ∀ v, v ∉ W → ENNReal.ofReal (φ v) = 0 := by
    intro v hv
    rw [image_eq_zero_of_notMem_tsupport fun h => hv (hs h), ENNReal.ofReal_zero]
  have hψs0 : ∀ v, v ∉ W → ENNReal.ofReal (φ (T s v)) = 0 :=
    fun v hv => hψ0 _ fun h => hv ((hTW s v).1 h)
  have hD := continuous_lintegral hF hφ hc (hs.trans hWU) h0
  have hD' := continuous_lintegral hF hφs hcs (hss.trans hWU) (fun v => h0 _)
  have hDs : Continuous fun b => ∫⁻ v, ENNReal.ofReal (φ v) ∂(fib (b + s)) :=
    hD.comp (continuous_add_const s)
  refine GlobalTheory.T.continuous_densities_eq_of_integrals_on_compacts X ν Set.univ isOpen_univ _ _ hD'.continuousOn hDs.continuousOn
    (fun S hS _ => ?_) c (Set.mem_univ c)
  have hSm := hS.measurableSet
  have hS'm : MeasurableSet ((fun x : X => x - s) ⁻¹' S) :=
    (continuous_sub_right s).measurable hSm
  have e1 := GlobalTheory.CompanionTheory.SW.FibreUniq.lintegral_preimage hι hg hf hW hWU hF
    (fun v => ENNReal.ofReal (φ (T s v))) (hψm.comp (hTm s)) hψs0 S hSm
  have e2 := GlobalTheory.CompanionTheory.SW.FibreUniq.lintegral_preimage hι hg hf hW hWU hF
    (fun v => ENNReal.ofReal (φ v)) hψm hψ0 _ hS'm
  have hAm : Measurable ((g ⁻¹' ((fun x : X => x - s) ⁻¹' S)).indicator
      fun v => ENNReal.ofReal (φ v)) := hψm.indicator (hg.measurable hS'm)
  have hA0 : ∀ v, v ∉ W → (g ⁻¹' ((fun x : X => x - s) ⁻¹' S)).indicator
      (fun v => ENNReal.ofReal (φ v)) v = 0 :=
    fun v hv => Set.indicator_apply_eq_zero.2 fun _ => hψ0 v hv
  have hB0 : ∀ v, v ∉ W → (g ⁻¹' S).indicator (fun v => ENNReal.ofReal (φ (T s v))) v = 0 :=
    fun v hv => Set.indicator_apply_eq_zero.2 fun _ => hψs0 v hv
  have hcomp : ∀ v, (g ⁻¹' S).indicator (fun v => ENNReal.ofReal (φ (T s v))) v =
      (g ⁻¹' ((fun x : X => x - s) ⁻¹' S)).indicator (fun v => ENNReal.ofReal (φ v)) (T s v) := by
    intro v
    by_cases hv : v ∈ W
    · have hiff : T s v ∈ g ⁻¹' ((fun x : X => x - s) ⁻¹' S) ↔ v ∈ g ⁻¹' S := by
        simp only [Set.mem_preimage, hgT s v hv, add_sub_cancel_right]
      by_cases hvS : v ∈ g ⁻¹' S
      · rw [Set.indicator_of_mem hvS, Set.indicator_of_mem (hiff.2 hvS)]
      · rw [Set.indicator_of_notMem hvS, Set.indicator_of_notMem (fun h => hvS (hiff.1 h))]
    · rw [hB0 v hv, hA0 _ fun h => hv ((hTW s v).1 h)]
  have hmid : ∫⁻ v in W, (g ⁻¹' S).indicator (fun v => ENNReal.ofReal (φ (T s v))) v ∂μ =
      ∫⁻ v in W, (g ⁻¹' ((fun x : X => x - s) ⁻¹' S)).indicator
        (fun v => ENNReal.ofReal (φ v)) v ∂μ := by
    rw [setLIntegral_eq_lintegral hW.measurableSet hB0,
      setLIntegral_eq_lintegral hW.measurableSet hA0]
    simp only [hcomp]
    rw [← lintegral_map hAm (hTm s), hTμ s]
  have hpre : (fun x : X => x + s) ⁻¹' ((fun x : X => x - s) ⁻¹' S) = S := by
    ext x
    simp
  have htr := (measurePreserving_add_right ν s).setLIntegral_comp_preimage hS'm hD.measurable
  rw [hpre] at htr
  rw [← e1, hmid, e2, ← htr]

theorem fib_ne_zero : ∀ (V X Y : Type) [TopologicalSpace V] [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V] [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X] [LocallyCompactSpace X] [SecondCountableTopology X] [T2Space X] [MeasurableSpace X] [BorelSpace X] (μ : Measure V) (ν : Measure X) [IsLocallyFiniteMeasure μ] [μ.IsOpenPosMeasure] [ν.IsAddHaarMeasure] (f : V → Y) (g : V → X) (ι : X → Y), Function.Injective ι → Continuous g → (∀ v, f v = ι (g v)) → ∀ (U W : Set V), IsOpen W → W ⊆ U → W.Nonempty → ∀ fib : X → Measure V, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι U ν Set.univ fib → ∀ T : X → V → V, (∀ s, Measurable (T s)) → (∀ s, μ.map (T s) = μ) → (∀ s, ContinuousOn (T s) W) → (∀ s v, T s v ∈ W ↔ v ∈ W) → (∀ s, ∀ v ∈ W, T (-s) (T s v) = v) → (∀ s, ∀ v ∈ W, g (T s v) = g v + s) → ∀ b : X, fib b ≠ 0 := by
  intro V X Y _ _ _ _ _ _ _ _ _ _ _ _ _ _ μ ν _ _ _ f g ι hι hg hf U W hW hWU hne fib hF T hTm hTμ
    hTc hTW hinv hgT b hb
  obtain ⟨v₀, hv₀⟩ := hne
  obtain ⟨φ, hφ, hc, hs, h0, -, h1⟩ := GlobalTheory.CompanionTheory.SW.FibreFam.exists_bump
    (isCompact_singleton (x := v₀)) hW (Set.singleton_subset_iff.2 hv₀)
  have hzero : ∀ c, ∫⁻ v, ENNReal.ofReal (φ v) ∂(fib c) = 0 := by
    intro c
    have key := lintegral_shift hι hg hf hW hWU hF hTm hTμ hTc hTW hinv hgT hφ hc hs h0 (c - b) b
    rw [add_sub_cancel] at key
    rw [← key, hb]
    simp
  have hm : Measurable fun v => ENNReal.ofReal (φ v) :=
    ENNReal.measurable_ofReal.comp hφ.measurable
  have h2 := hF.2.1 _ hm
  simp only [hzero, lintegral_zero] at h2
  have h3 : ∫⁻ v in W, ENNReal.ofReal (φ v) ∂μ = 0 :=
    le_antisymm (h2 ▸ lintegral_mono_set hWU) bot_le
  have hae := (ae_restrict_iff' hW.measurableSet).1 ((lintegral_eq_zero_iff hm).1 h3)
  have hOpen : IsOpen ({v | 0 < φ v} ∩ W) := (isOpen_lt continuous_const hφ).inter hW
  have hpos : 0 < μ ({v | 0 < φ v} ∩ W) :=
    hOpen.measure_pos μ ⟨v₀, by simp [h1 v₀ rfl], hv₀⟩
  have hnull := ae_iff.1 hae
  refine hpos.ne' (measure_mono_null ?_ hnull)
  intro v hv
  rw [Set.mem_setOf_eq]
  intro hcon
  have h4 := hcon hv.2
  simp only [Pi.zero_apply, ENNReal.ofReal_eq_zero] at h4
  exact absurd hv.1 (not_lt.2 h4)

end GlobalTheory.CompanionTheory.SW.FibreShift
