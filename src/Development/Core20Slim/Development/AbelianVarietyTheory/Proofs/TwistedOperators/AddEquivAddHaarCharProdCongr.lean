module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.MulVecCEApply
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Basic.ENNReal.Action
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.ENNReal.Operations
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.Nonempty
public import Mathlib.Data.Set.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.AEMeasurable
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import Mathlib.MeasureTheory.Measure.Haar.MulEquivHaarChar
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Module
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.Regular
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
public import Mathlib.MeasureTheory.Measure.WithDensity
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
public import Mathlib.Topology.Compactness.SigmaCompact
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.Metrizable.Basic
public import Mathlib.Topology.Metrizable.Urysohn
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.Separation.Regular
public import Mathlib.Topology.Sets.Compacts

@[expose] public section

open MeasureTheory Topology Matrix NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.ModuLR
open scoped NNReal ENNReal TensorProduct

namespace GlobalTheory.ModuLR

theorem addEquivAddHaarChar_prodCE (G₁ G₂ : Type) [AddCommGroup G₁] [TopologicalSpace G₁]
    [IsTopologicalAddGroup G₁] [LocallyCompactSpace G₁] [T2Space G₁] [SecondCountableTopology G₁]
    [MeasurableSpace G₁] [BorelSpace G₁] [AddCommGroup G₂] [TopologicalSpace G₂]
    [IsTopologicalAddGroup G₂] [LocallyCompactSpace G₂] [T2Space G₂] [SecondCountableTopology G₂]
    [MeasurableSpace G₂] [BorelSpace G₂] (e₁ : G₁ ≃ₜ+ G₁) (e₂ : G₂ ≃ₜ+ G₂) :
    addEquivAddHaarChar (prodCE e₁ e₂) = addEquivAddHaarChar e₁ * addEquivAddHaarChar e₂ := by
  set μ₁ : Measure G₁ := Measure.addHaar
  set μ₂ : Measure G₂ := Measure.addHaar
  set μ : Measure (G₁ × G₂) := μ₁.prod μ₂
  have hμ : μ.IsAddHaarMeasure := by infer_instance
  have hreg : μ.Regular := by infer_instance
  set φ := prodCE e₁ e₂
  have h1 := addEquivAddHaarChar_smul_map μ₁ e₁
  have h2 := addEquivAddHaarChar_smul_map μ₂ e₂
  have h := addEquivAddHaarChar_smul_map μ φ
  have hm1 : (μ₁.map e₁).IsAddHaarMeasure := e₁.isAddHaarMeasure_map μ₁
  have hm2 : (μ₂.map e₂).IsAddHaarMeasure := e₂.isAddHaarMeasure_map μ₂
  have hmap : μ.map φ = (μ₁.map e₁).prod (μ₂.map e₂) := by
    have := Measure.map_prod_map μ₁ μ₂ e₁.continuous.measurable e₂.continuous.measurable
    exact this.symm
  have hc : (addEquivAddHaarChar e₁ * addEquivAddHaarChar e₂) • μ.map φ = μ := by
    rw [hmap]
    conv_rhs => rw [show μ = μ₁.prod μ₂ from rfl, ← h1, ← h2]
    rw [mul_smul]
    rw [Measure.prod_smul_left, Measure.prod_smul_right]
  have hν : (μ.map φ).IsAddHaarMeasure := φ.isAddHaarMeasure_map μ
  obtain ⟨K, hK, hK0⟩ := exists_compact_mem_nhds (0 : G₁ × G₂)
  have hpos : (μ.map φ) K ≠ 0 := (Measure.measure_pos_of_mem_nhds _ hK0).ne'
  have hfin : (μ.map φ) K ≠ ∞ := hK.measure_lt_top.ne
  have key := congrArg (fun m : Measure (G₁ × G₂) => m K) (h.trans hc.symm)
  simp only [Measure.smul_apply, Measure.nnreal_smul_coe_apply] at key
  have := (ENNReal.mul_left_inj hpos hfin).1 key
  exact_mod_cast this

end GlobalTheory.ModuLR
