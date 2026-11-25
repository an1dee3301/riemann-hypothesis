module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
public import Init.Classical
public import Init.Core
public import Init.Data.Subtype.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.PropLemmas
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Notation.Indicator
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Countable.Defs
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.ENNReal.Inv
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SProd
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Attach
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Sets
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.MeasurableSpace.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.MeasurableSpace.Pi
public import Mathlib.MeasureTheory.Measure.CompleteLattice
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Module
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
public import Mathlib.MeasureTheory.PiSystem
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.GaugeEx.ProdInt

theorem map_eq_smul_prod {ι Z Zi : Type} {Zv : ι → Type} [MeasurableSpace Z] [MeasurableSpace Zi]
    [∀ v, MeasurableSpace (Zv v)] (ρ : Measure Z) (mi : Measure Zi) (mv : ∀ v, Measure (Zv v))
    [SigmaFinite mi] [∀ v, SigmaFinite (mv v)] (pi : Z → Zi) (pv : ∀ v, Z → Zv v)
    (hpi : Measurable pi) (hpv : ∀ v, Measurable (pv v)) (S : Finset ι) (c : ℝ≥0∞) (hc : c ≠ ⊤)
    (h : ∀ (fi : Zi → ℝ≥0∞) (fv : ∀ v, Zv v → ℝ≥0∞), Measurable fi → (∀ v, Measurable (fv v)) →
      ∫⁻ X, fi (pi X) * ∏ v ∈ S, fv v (pv v X) ∂ρ =
        (∫⁻ Y, fi Y ∂mi) * (∏ v ∈ S, ∫⁻ Y, fv v Y ∂(mv v)) * c) :
    ρ.map (fun X => (pi X, fun v : S => pv v X)) = c • mi.prod (Measure.pi fun v : S => mv v) := by
  classical
  have hT : Measurable (fun X => (pi X, fun v : S => pv v X)) :=
    hpi.prodMk (Measurable.of_eval fun v => hpv v)
  by_cases hc0 : c = 0
  · have := h (fun _ => 1) (fun _ _ => 1) measurable_const (fun _ => measurable_const)
    simp only [hc0, mul_zero, Finset.prod_const_one, mul_one, lintegral_const, one_mul,
      Measure.measure_univ_eq_zero] at this
    simp [this, hc0]
  have key : mi.prod (Measure.pi fun v : S => mv v) =
      c⁻¹ • ρ.map (fun X => (pi X, fun v : S => pv v X)) := by
    refine Measure.prod_eq_generateFrom (C := {s | MeasurableSet s})
      (D := Set.pi Set.univ '' Set.pi Set.univ fun v : S => {s : Set (Zv v) | MeasurableSet s})
      MeasurableSpace.generateFrom_measurableSet generateFrom_pi
      MeasurableSpace.isPiSystem_measurableSet isPiSystem_pi mi.toFiniteSpanningSetsIn
      (Measure.FiniteSpanningSetsIn.pi fun v : S => (mv v).toFiniteSpanningSetsIn) ?_
    rintro s hs _ ⟨t, ht, rfl⟩
    have hs' : MeasurableSet s := hs
    have ht' : ∀ v : S, MeasurableSet (t v) := fun v => ht v (Set.mem_univ _)
    let fv : ∀ v, Zv v → ℝ≥0∞ := fun v => if hv : v ∈ S then (t ⟨v, hv⟩).indicator 1 else 0
    have hfv : ∀ v, Measurable (fv v) := by
      intro v
      by_cases hv : v ∈ S
      · simp only [fv, dif_pos hv]
        exact measurable_one.indicator (ht' _)
      · simp only [fv, dif_neg hv]
        exact measurable_zero
    have hfv' : ∀ v : S, fv v = (t v).indicator 1 := fun v => by simp only [fv, dif_pos v.2]
    have h1 := h (s.indicator 1) fv (measurable_one.indicator hs') hfv
    have hm : MeasurableSet (s ×ˢ Set.pi Set.univ t) :=
      hs'.prod (MeasurableSet.univ_pi ht')
    rw [Measure.smul_apply, Measure.map_apply hT hm, ← lintegral_indicator_one (hT hm), Measure.pi_pi]
    have h2 : ∀ X, ((fun X => (pi X, fun v : S => pv v X)) ⁻¹' (s ×ˢ Set.pi Set.univ t)).indicator
        (1 : Z → ℝ≥0∞) X = s.indicator 1 (pi X) * ∏ v ∈ S, fv v (pv v X) := by
      intro X
      rw [← Finset.prod_coe_sort S]
      simp only [hfv']
      by_cases hX : pi X ∈ s
      · by_cases hY : ∀ v : S, pv v X ∈ t v
        · rw [Set.indicator_of_mem (by simpa [hX] using hY)]
          simp [hX, hY]
        · rw [Set.indicator_of_notMem (by simpa [hX] using hY)]
          push_neg at hY
          obtain ⟨v, hv⟩ := hY
          rw [Finset.prod_eq_zero (Finset.mem_univ v) (by simp [hv])]
          simp
      · rw [Set.indicator_of_notMem (by simp [hX])]
        simp [hX]
    simp_rw [h2]
    rw [h1, ← Finset.prod_coe_sort S]
    simp only [hfv', lintegral_indicator_one hs', lintegral_indicator_one (ht' _), smul_eq_mul]
    rw [mul_comm c⁻¹, mul_assoc, ENNReal.mul_inv_cancel hc0 hc, mul_one]
  rw [key, smul_smul, ENNReal.mul_inv_cancel hc0 hc, one_smul]

theorem integral_tensor {ι Z Zi : Type} {Zv : ι → Type} [MeasurableSpace Z] [MeasurableSpace Zi]
    [∀ v, MeasurableSpace (Zv v)] (ρ : Measure Z) (mi : Measure Zi) (mv : ∀ v, Measure (Zv v))
    [SigmaFinite mi] [∀ v, SigmaFinite (mv v)] (pi : Z → Zi) (pv : ∀ v, Z → Zv v)
    (hpi : Measurable pi) (hpv : ∀ v, Measurable (pv v)) (S : Finset ι) (c : ℝ≥0∞) (hc : c ≠ ⊤)
    (h : ∀ (fi : Zi → ℝ≥0∞) (fv : ∀ v, Zv v → ℝ≥0∞), Measurable fi → (∀ v, Measurable (fv v)) →
      ∫⁻ X, fi (pi X) * ∏ v ∈ S, fv v (pv v X) ∂ρ =
        (∫⁻ Y, fi Y ∂mi) * (∏ v ∈ S, ∫⁻ Y, fv v Y ∂(mv v)) * c)
    (Φi : Zi → ℂ) (Φv : ∀ v, Zv v → ℂ) (hi : Integrable Φi mi) (hv : ∀ v, Integrable (Φv v) (mv v)) :
    Integrable (fun X => Φi (pi X) * ∏ v ∈ S, Φv v (pv v X)) ρ ∧
      ∫ X, Φi (pi X) * ∏ v ∈ S, Φv v (pv v X) ∂ρ =
        (∫ Y, Φi Y ∂mi) * ((∏ v ∈ S, ∫ Y, Φv v Y ∂(mv v)) * (c.toReal : ℂ)) := by
  have hT : Measurable (fun X => (pi X, fun v : S => pv v X)) :=
    hpi.prodMk (Measurable.of_eval fun v => hpv v)
  have hmap := map_eq_smul_prod ρ mi mv pi pv hpi hpv S c hc h
  let G : Zi × (∀ v : S, Zv v) → ℂ := fun Y => Φi Y.1 * ∏ v : S, Φv v (Y.2 v)
  have hG : Integrable G (mi.prod (Measure.pi fun v : S => mv v)) :=
    hi.mul_prod (Integrable.fintype_prod_dep (f := fun v : S => Φv v) fun v => hv v)
  have hG' : Integrable G (ρ.map (fun X => (pi X, fun v : S => pv v X))) := by
    rw [hmap]; exact hG.smul_measure hc
  have he : (fun X => Φi (pi X) * ∏ v ∈ S, Φv v (pv v X)) =
      G ∘ (fun X => (pi X, fun v : S => pv v X)) := by
    funext X
    simp only [G, Function.comp]
    rw [← Finset.prod_coe_sort S]
  rw [he]
  refine ⟨(integrable_map_measure hG'.aestronglyMeasurable hT.aemeasurable).1 hG', ?_⟩
  have := integral_map hT.aemeasurable hG'.aestronglyMeasurable
  simp only [Function.comp_def]
  rw [← this, hmap, integral_smul_measure]
  simp only [G]
  rw [integral_prod_mul Φi (fun Y : ∀ v : S, Zv v => ∏ v : S, Φv v (Y v)),
    integral_fintype_prod_eq_prod (fun v : S => Φv v), ← Finset.prod_coe_sort S, Complex.real_smul]
  ring



end GlobalTheory.GaugeEx.ProdInt
