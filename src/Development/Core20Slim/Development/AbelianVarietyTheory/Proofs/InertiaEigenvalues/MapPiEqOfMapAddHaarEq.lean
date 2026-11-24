module

public import Mathlib
public import Init.Core
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Basic.Countable.Defs
public import Mathlib.Basic.ENNReal.Action
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.Nonempty
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Module
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.Sets.Compacts

@[expose] public section

open MeasureTheory

namespace GlobalTheory

theorem map_pi_eq_of_map_addHaar_eq (G : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (φ : G →+ G) (hφ : Continuous φ)
    (h : ∀ ν : Measure G, ν.IsAddHaarMeasure → ν.map φ = ν) (m : ℕ)
    (μ : @Measure (Fin m → G) (borel _))
    (hμ : @Measure.IsAddHaarMeasure (Fin m → G) _ _ (borel _) μ) :
    @Measure.map _ _ (borel _) (borel _) (fun x i => φ (x i)) μ = μ := by
  have hb : (MeasurableSpace.pi : MeasurableSpace (Fin m → G)) = borel _ := BorelSpace.measurable_eq
  revert μ hμ
  rw [← hb]
  intro μ hμ
  let ν : Measure G := Measure.addHaar
  have hν : ν.IsAddHaarMeasure := inferInstance
  have hp : MeasurePreserving φ ν ν := ⟨hφ.measurable, h ν hν⟩
  have hpi : MeasurePreserving (fun (x : Fin m → G) i => φ (x i)) (Measure.pi fun _ => ν) (Measure.pi fun _ => ν) :=
    measurePreserving_pi _ _ (fun _ => hp)
  have hH : (Measure.pi fun _ : Fin m => ν).IsAddHaarMeasure := inferInstance
  have he := Measure.isAddLeftInvariant_eq_smul μ (Measure.pi fun _ : Fin m => ν)
  generalize Measure.addHaarScalarFactor μ (Measure.pi fun _ : Fin m => ν) = c at he
  subst he
  rw [Measure.map_smul c hpi.measurable.aemeasurable, hpi.map_eq]

end GlobalTheory
