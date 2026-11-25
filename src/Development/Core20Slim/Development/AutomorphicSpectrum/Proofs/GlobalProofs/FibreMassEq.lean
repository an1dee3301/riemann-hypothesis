module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.GlobalProofs.CoefS
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CompletionIsLocalRing
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRing
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHaarMeasure
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ContinuousHermScal
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HaarMeasureNonunitsNull
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.IsFibreFamilyLength
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Classical
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.NeZero
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Notation.Indicator
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.ENNReal.Operations
public import Mathlib.Basic.ENNReal.Real
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.MeasureTheory.OuterMeasure.AE
public import Mathlib.MeasureTheory.OuterMeasure.Basic
public import Mathlib.Order.Basic
public import Mathlib.Order.BoundedOrder.Basic
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Filter.SmallSets
public import Mathlib.Order.Filter.Tendsto
public import Mathlib.Order.Lattice
public import Mathlib.Order.Notation
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
public import Mathlib.Topology.Algebra.Support
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV
open scoped TensorProduct ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.OneV.AvgV

theorem fibre_mass_eq {V R : Type} [TopologicalSpace V] [MeasurableSpace V] [TopologicalSpace R] [MeasurableSpace R]
    (μ : Measure V) (ν : Measure R) (q : V → R) (hq : Measurable q) (B : Set R) (fib : R → Measure V)
    (h : IsFibreFamily μ q id Set.univ ν B fib) {A : Set V} {S : Set R} (hA : MeasurableSet A)
    (hS : MeasurableSet S) : μ (A ∩ q ⁻¹' S) = ∫⁻ s in S, fib s A ∂ν := by
  obtain ⟨h1, h2, -⟩ := h
  have hT : MeasurableSet (A ∩ q ⁻¹' S) := hA.inter (hq hS)
  have e := h2 ((A ∩ q ⁻¹' S).indicator 1) (measurable_one.indicator hT)
  simp only [Measure.restrict_univ, lintegral_indicator_one hT] at e
  rw [e, ← lintegral_indicator hS]
  refine lintegral_congr fun b => ?_
  have hae : ∀ᵐ x ∂(fib b), q x = b := by
    refine measure_mono_null ?_ (h1 b)
    intro x hx hx'
    exact hx hx'.1
  by_cases hb : b ∈ S
  · rw [Set.indicator_of_mem hb]
    refine measure_congr ?_
    filter_upwards [hae] with x hx
    refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
    show q x ∈ S
    rwa [hx]
  · rw [Set.indicator_of_notMem hb]
    refine measure_mono_null (t := {x | ¬ q x = b}) ?_ hae
    intro x hx hxb
    apply hb
    rw [← hxb]
    exact hx.2

theorem tendsto_mean {R : Type} [TopologicalSpace R] [MeasurableSpace R] (ν : Measure R) (G : R → ℝ≥0∞) (c : R)
    (hG : ContinuousAt (fun s => (G s).toReal) c) (hfin : ∀ᶠ s in nhds c, G s ≠ ⊤) (S : ℕ → Set R)
    (hS : ∀ k, MeasurableSet (S k)) (hl : Filter.Tendsto S Filter.atTop (nhds c).smallSets)
    (hpos : ∀ k, ν (S k) ≠ 0) (htop : ∀ k, ν (S k) ≠ ⊤) :
    Filter.Tendsto (fun k => (∫⁻ s in S k, G s ∂ν).toReal / (ν (S k)).toReal) Filter.atTop
      (nhds (G c).toReal) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hN : {s | G s ≠ ⊤ ∧ dist (G s).toReal (G c).toReal < ε / 2} ∈ nhds c :=
    Filter.inter_mem hfin (hG.eventually (Metric.ball_mem_nhds _ (half_pos hε)))
  have hev := hl.eventually (Filter.eventually_smallSets_subset.2 hN)
  filter_upwards [hev] with k hk
  set g := (G c).toReal with hg
  have hg0 : 0 ≤ g := ENNReal.toReal_nonneg
  set n := ν (S k) with hn
  have hnr : 0 < n.toReal := ENNReal.toReal_pos (hpos k) (htop k)
  have hup : ∫⁻ s in S k, G s ∂ν ≤ ENNReal.ofReal (g + ε / 2) * n := by
    rw [hn, ← setLIntegral_const]
    refine setLIntegral_mono' (hS k) fun s hs => ?_
    obtain ⟨h1, h2⟩ := hk hs
    rw [← ENNReal.ofReal_toReal h1]
    refine ENNReal.ofReal_le_ofReal ?_
    have := (abs_lt.1 (Real.dist_eq _ _ ▸ h2)).2
    linarith
  have hlo : ENNReal.ofReal (g - ε / 2) * n ≤ ∫⁻ s in S k, G s ∂ν := by
    rw [hn, ← setLIntegral_const]
    refine setLIntegral_mono' (hS k) fun s hs => ?_
    obtain ⟨h1, h2⟩ := hk hs
    rw [← ENNReal.ofReal_toReal h1]
    refine ENNReal.ofReal_le_ofReal ?_
    have := (abs_lt.1 (Real.dist_eq _ _ ▸ h2)).1
    linarith
  have hfinU : ENNReal.ofReal (g + ε / 2) * n ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top (htop k)
  have hup' : (∫⁻ s in S k, G s ∂ν).toReal ≤ (g + ε / 2) * n.toReal := by
    have := ENNReal.toReal_mono hfinU hup
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at this
  have hlo' : (g - ε / 2) * n.toReal ≤ (∫⁻ s in S k, G s ∂ν).toReal := by
    have := ENNReal.toReal_mono (ne_top_of_le_ne_top hfinU hup) hlo
    rw [ENNReal.toReal_mul] at this
    refine le_trans ?_ this
    refine mul_le_mul_of_nonneg_right ?_ hnr.le
    rw [ENNReal.toReal_ofReal']
    exact le_max_left _ _
  rw [Real.dist_eq, abs_lt]
  constructor
  · have : g - ε / 2 ≤ (∫⁻ s in S k, G s ∂ν).toReal / n.toReal := (le_div_iff₀ hnr).2 hlo'
    linarith
  · have : (∫⁻ s in S k, G s ∂ν).toReal / n.toReal ≤ g + ε / 2 := (div_le_iff₀ hnr).2 hup'
    linarith

end GlobalTheory.CompanionTheory.Hypotheses₂.OneV.AvgV

