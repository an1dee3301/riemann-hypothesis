module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.MulVecCEApply
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
public import Init.Classical
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Basic.ENNReal.Action
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.ENNReal.Operations
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.IsEmpty.Basic
public import Mathlib.Basic.IsEmpty.Defs
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.Nonempty
public import Mathlib.Data.Set.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Group.Arithmetic
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.MeasurableSpace.Embedding
public import Mathlib.MeasureTheory.Measure.Comap
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import Mathlib.MeasureTheory.Measure.Haar.MulEquivHaarChar
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Module
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.MeasureTheory.Measure.Regular
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Notation
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.Compactness.Paracompact
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.Metrizable.Basic
public import Mathlib.Topology.Metrizable.Urysohn
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.Separation.Regular
public import Mathlib.Topology.Sets.Compacts

@[expose] public section

open MeasureTheory Topology Matrix NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.ModuLR
open scoped NNReal ENNReal TensorProduct

namespace GlobalTheory.HaarOpenEmb

theorem nnreal_smul_cancel {Y : Type} [TopologicalSpace Y] [MeasurableSpace Y] [LocallyCompactSpace Y]
    (ρ : Measure Y) [IsFiniteMeasureOnCompacts ρ] [ρ.IsOpenPosMeasure] [Nonempty Y] {a b : ℝ≥0}
    (h : a • ρ = b • ρ) : a = b := by
  obtain ⟨y⟩ := (inferInstance : Nonempty Y)
  obtain ⟨K, hK, hKn⟩ := exists_compact_mem_nhds y
  have h0 : ρ K ≠ 0 := (Measure.measure_pos_of_mem_nhds ρ hKn).ne'
  have hT : ρ K ≠ ∞ := hK.measure_lt_top.ne
  have e := congrArg (fun μ : Measure Y => μ K) h
  simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at e
  exact_mod_cast (ENNReal.mul_left_inj h0 hT).1 e

theorem addEquivAddHaarChar_eq_of_isOpenEmbedding :
    ∀ (G G' : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [LocallyCompactSpace G] [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [AddCommGroup G'] [TopologicalSpace G'] [IsTopologicalAddGroup G'] [LocallyCompactSpace G'] [T2Space G'] [SecondCountableTopology G'] [MeasurableSpace G'] [BorelSpace G'] (j : G' →+ G), IsOpenEmbedding j → ∀ (e : G ≃ₜ+ G) (e' : G' ≃ₜ+ G'), (∀ x, e (j x) = j (e' x)) → addEquivAddHaarChar e = addEquivAddHaarChar e' := by
  intro G G' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ j hj e e' hcomm
  by_cases hne : Nonempty G'
  swap
  · have : IsEmpty G' := not_nonempty_iff.1 hne
    exact absurd ⟨0⟩ hne
  let μ : Measure G := Measure.addHaar
  let ν : Measure G' := μ.comap j
  haveI : ν.IsAddHaarMeasure := Measure.IsAddHaarMeasure.comap (mH := inferInstance) μ hj
  haveI : ν.Regular := inferInstance
  have hjm : ∀ s, MeasurableSet s → MeasurableSet ((j : G' → G) '' s) :=
    fun s hs => hj.measurableEmbedding.measurableSet_image' hs
  have hem : ∀ s, MeasurableSet s → MeasurableSet ((e : G → G) '' s) :=
    fun s hs => e.toHomeomorph.measurableEmbedding.measurableSet_image' hs
  have he'm : ∀ s, MeasurableSet s → MeasurableSet ((e' : G' → G') '' s) :=
    fun s hs => e'.toHomeomorph.measurableEmbedding.measurableSet_image' hs
  have h1 := addEquivAddHaarChar_smul_eq_comap μ e
  have h2 := addEquivAddHaarChar_smul_eq_comap ν e'
  have hfun : (e : G → G) ∘ (j : G' → G) = (j : G' → G) ∘ (e' : G' → G') := funext hcomm
  have key : addEquivAddHaarChar e • ν = addEquivAddHaarChar e' • ν := by
    rw [h2]
    change addEquivAddHaarChar e • μ.comap j = (μ.comap j).comap e'
    rw [Measure.comap_comap he'm hj.injective hjm, ← hfun,
      ← Measure.comap_comap hjm e.injective hem, ← h1]
    have hs : ∀ (c : ℝ≥0) (m : Measure G), c • m = (c : ℝ≥0∞) • m := fun c m => by
      ext s hs; rw [Measure.smul_apply, Measure.smul_apply]; rfl
    have hs' : ∀ (c : ℝ≥0) (m : Measure G'), c • m = (c : ℝ≥0∞) • m := fun c m => by
      ext s hs; rw [Measure.smul_apply, Measure.smul_apply]; rfl
    rw [hs, hs', Measure.comap_smul]
  exact nnreal_smul_cancel ν key

end GlobalTheory.HaarOpenEmb
