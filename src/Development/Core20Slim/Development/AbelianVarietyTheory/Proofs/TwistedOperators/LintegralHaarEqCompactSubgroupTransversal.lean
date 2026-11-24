module

public import Mathlib
public import Init.Classical
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Order.Lemmas
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.IsApply
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Notation.Indicator
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.Group.Indicator
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.IsBotOne
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.ZeroLEOne
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Basic.ENNReal.Action
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Group.Arithmetic
public import Mathlib.MeasureTheory.Group.Defs
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map
public import Mathlib.MeasureTheory.MeasurableSpace.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.CompleteLattice
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Module
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
public import Mathlib.MeasureTheory.OuterMeasure.AE
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.Basic
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Notation
public import Mathlib.Order.RelClasses
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Separation.Hausdorff

@[expose] public section

open MeasureTheory

namespace GlobalTheory.Twist

theorem lintegral_haar_eq_transversal (G E : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    [MeasurableSpace E] (μ mK : Measure G) [μ.IsHaarMeasure] [μ.IsInvInvariant]
    [IsProbabilityMeasure mK] (lam : Measure E) [SFinite lam] (K : Set G) (e : E → G)
    (he : Measurable e) (hK : mK Kᶜ = 0)
    (hinv : ∀ k ∈ K, Measure.map (fun x => x * k) mK = mK) (hlam : lam ≠ 0)
    (hfin : ∀ C : Set G, IsCompact C → lam {B | ∃ k ∈ K, k * e B ∈ C} < ⊤)
    (hact : ∀ g : G, ∃ ψ : E → E, Measurable ψ ∧ Measure.map ψ lam = lam ∧
      ∀ B, ∃ κ ∈ K, e B * g = κ * e (ψ B)) :
    ∃ c : ℝ, 0 < c ∧ ∀ f : G → ENNReal, Measurable f →
      ∫⁻ g, f g ∂μ = ENNReal.ofReal c * ∫⁻ B, ∫⁻ k, f (k * e B) ∂mK ∂lam := by
  have hm : Measurable (fun z : E × G => z.2 * e z.1) :=
    measurable_snd.mul (he.comp measurable_fst)
  set ν : Measure G := Measure.map (fun z : E × G => z.2 * e z.1) (lam.prod mK) with hν
  have hint : ∀ f : G → ENNReal, Measurable f →
      ∫⁻ g, f g ∂ν = ∫⁻ B, ∫⁻ k, f (k * e B) ∂mK ∂lam := by
    intro f hf
    rw [hν, lintegral_map hf hm]
    exact lintegral_prod (fun z : E × G => f (z.2 * e z.1)) (hf.comp hm).aemeasurable
  have hH : ∀ f : G → ENNReal, Measurable f →
      Measurable (fun B => ∫⁻ k, f (k * e B) ∂mK) := by
    intro f hf
    exact Measurable.lintegral_prod_right' (f := fun z : E × G => f (z.2 * e z.1)) (hf.comp hm)
  have hR : ν.IsMulRightInvariant := by
    refine ⟨fun g => ?_⟩
    obtain ⟨ψ, hψ, hψl, hψe⟩ := hact g
    refine Measure.ext_of_lintegral _ (fun f hf => ?_)
    have hg : Measurable (fun x : G => x * g) := measurable_mul_const g
    rw [lintegral_map hf hg, hint (fun x => f (x * g)) (hf.comp hg), hint f hf]
    have h1 : ∀ B, ∫⁻ k, f (k * e B * g) ∂mK = ∫⁻ k, f (k * e (ψ B)) ∂mK := by
      intro B
      obtain ⟨κ, hκ, hk⟩ := hψe B
      have h2 := lintegral_map (μ := mK) (f := fun x => f (x * e (ψ B))) (g := fun x => x * κ)
        (hf.comp (measurable_mul_const _)) (measurable_mul_const κ)
      rw [hinv κ hκ] at h2
      rw [h2]
      simp only [mul_assoc, hk]
    simp only [h1]
    have h3 := lintegral_map (μ := lam) (hH f hf) hψ
    rw [hψl] at h3
    exact h3.symm
  have hF : IsFiniteMeasureOnCompacts ν := by
    refine ⟨fun C hC => ?_⟩
    have hCm : MeasurableSet C := hC.measurableSet
    have h1 := hint (C.indicator 1) (measurable_one.indicator hCm)
    rw [lintegral_indicator_one hCm] at h1
    rw [h1]
    set S := {B | ∃ k ∈ K, k * e B ∈ C} with hS
    refine lt_of_le_of_lt ?_ (hfin C hC)
    rw [← measure_toMeasurable, ← lintegral_indicator_one (measurableSet_toMeasurable _ _)]
    refine lintegral_mono (fun B => ?_)
    by_cases hB : B ∈ toMeasurable lam S
    · rw [Set.indicator_of_mem hB]
      calc ∫⁻ k, C.indicator (1 : G → ENNReal) (k * e B) ∂mK ≤ ∫⁻ _k, 1 ∂mK :=
            lintegral_mono (fun k => Set.indicator_le_self' (fun _ _ => zero_le_one) _)
        _ = 1 := by simp
    · rw [Set.indicator_of_notMem hB]
      have hB' : B ∉ S := fun h => hB (subset_toMeasurable _ _ h)
      have hae : ∀ᵐ k ∂mK, k ∈ K := hK
      have : ∫⁻ k, C.indicator (1 : G → ENNReal) (k * e B) ∂mK = ∫⁻ _k, 0 ∂mK := by
        refine lintegral_congr_ae (hae.mono fun k hk => ?_)
        exact Set.indicator_of_notMem (fun h => hB' ⟨k, hk, h⟩) _
      simp [this]
  have hν0 : ν ≠ 0 := by
    intro h
    have h1 := hint (fun _ => 1) measurable_const
    rw [h] at h1
    simp at h1
    exact hlam (Measure.measure_univ_eq_zero.mp h1.symm)
  have hmul := Measure.isMulLeftInvariant_eq_smul ν.inv μ
  set c := Measure.haarScalarFactor ν.inv μ with hc
  have hνc : ν = c • μ := by
    have : ν.inv.inv = (c • μ).inv := by rw [← hmul]
    rw [Measure.inv_inv] at this
    rw [this]
    change Measure.map _ (c • μ) = _
    rw [Measure.map_smul (c := c) (f := Inv.inv)
      (measurable_inv.aemeasurable : AEMeasurable Inv.inv μ), Measure.map_inv_eq_self μ]
  have hc0 : c ≠ 0 := by
    intro h
    apply hν0
    rw [hνc, h, zero_smul]
  refine ⟨((c⁻¹ : NNReal) : ℝ), by exact_mod_cast inv_pos.mpr (pos_iff_ne_zero.mpr hc0), fun f hf => ?_⟩
  rw [← hint f hf, hνc, lintegral_smul_measure, ENNReal.ofReal_coe_nnreal, ENNReal.smul_def, smul_eq_mul,
    ← mul_assoc, ← ENNReal.coe_mul, inv_mul_cancel₀ hc0]
  simp

end GlobalTheory.Twist
