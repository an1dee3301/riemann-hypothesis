module

public import Mathlib
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Basic.ENNReal.Action
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.ENNReal.Operations
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Module
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Notation
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Separation.Hausdorff

@[expose] public section

namespace PositivityTheory.SiegelWeilFormula.OswLocFin

open MeasureTheory

theorem measurePreserving_of_addEquiv {G : Type*} [AddCommGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] [LocallyCompactSpace G] [T2Space G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (μ : MeasureTheory.Measure G) [μ.IsAddHaarMeasure]
    (e : G ≃+ G) (he : Continuous e) (he' : Continuous e.symm) (B : Set G) (hB : IsCompact B)
    (hB' : (interior B).Nonempty) (heB : e ⁻¹' B = B) :
    MeasureTheory.MeasurePreserving e μ μ := by
  have hm : Measurable e := he.measurable
  have : (μ.map e).IsAddHaarMeasure := e.isAddHaarMeasure_map μ he he'
  obtain ⟨c, hcμ⟩ : ∃ c : NNReal, μ.map e = c • μ := ⟨_, Measure.isAddLeftInvariant_eq_smul (μ.map e) μ⟩
  have hBm : MeasurableSet B := hB.isClosed.measurableSet
  have hval : μ.map e B = μ B := by rw [Measure.map_apply hm hBm, heB]
  have hpos : μ B ≠ 0 := (Measure.measure_pos_of_nonempty_interior μ hB').ne'
  have hfin : μ B ≠ ⊤ := hB.measure_lt_top.ne
  have hc : c = 1 := by
    have h1 := congrArg (fun ν : Measure G => ν B) hcμ
    simp only [Measure.smul_apply, hval, ENNReal.smul_def, smul_eq_mul] at h1
    have h2 : (c : ENNReal) * μ B = 1 * μ B := by rw [one_mul]; exact h1.symm
    have h3 : (c : ENNReal) = 1 := (ENNReal.mul_left_inj hpos hfin).1 h2
    exact_mod_cast h3
  refine ⟨hm, ?_⟩
  rw [hcμ, hc, one_smul]

end PositivityTheory.SiegelWeilFormula.OswLocFin
