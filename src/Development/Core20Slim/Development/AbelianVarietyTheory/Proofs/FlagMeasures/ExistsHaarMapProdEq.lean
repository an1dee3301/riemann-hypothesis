module

public import Mathlib
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Basic.ENNReal.Action
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.Nonempty
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Group.Arithmetic
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Module
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.Sets.Compacts

@[expose] public section

open MeasureTheory Measure
open scoped NNReal ENNReal

namespace GlobalTheory.St.HaarSplit

theorem exists_haar_map_prod_eq {A B C : Type*} [Group A] [Group B] [Group C]
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
    [IsTopologicalGroup A] [IsTopologicalGroup B] [IsTopologicalGroup C]
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    [BorelSpace A] [BorelSpace B] [BorelSpace C]
    [LocallyCompactSpace A] [LocallyCompactSpace B] [LocallyCompactSpace C]
    [SecondCountableTopology A] [SecondCountableTopology B] [SecondCountableTopology C]
    (e : (A × B) ≃ₜ* C) (μA : Measure A) [μA.IsHaarMeasure] (μC : Measure C) [μC.IsHaarMeasure] :
    ∃ μB : Measure B, μB.IsHaarMeasure ∧ (μA.prod μB).map e = μC := by
  let ν : Measure B := Measure.haar
  have : ((μA.prod ν).map e).IsHaarMeasure := ContinuousMulEquiv.isHaarMeasure_map (μA.prod ν) e
  have h := isMulLeftInvariant_eq_smul μC ((μA.prod ν).map e)
  have hc : 0 < haarScalarFactor μC ((μA.prod ν).map e) := haarScalarFactor_pos_of_isHaarMeasure _ _
  refine ⟨haarScalarFactor μC ((μA.prod ν).map e) • ν, IsHaarMeasure.nnreal_smul _ hc.ne', ?_⟩
  conv_rhs => rw [h]
  generalize haarScalarFactor μC ((μA.prod ν).map e) = c
  have he : AEMeasurable (e : A × B → C) (μA.prod ν) :=
    e.continuous.measurable.aemeasurable
  rw [← Measure.map_smul c he]
  congr 1
  rw [ENNReal.smul_def, ENNReal.smul_def, Measure.prod_smul_right]

end GlobalTheory.St.HaarSplit
