module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.AddEquivAddHaarCharProdCongr
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.MulVecCEApply
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
public import Init.Prelude
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.Haar.MulEquivHaarChar
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Separation.Hausdorff

@[expose] public section

open MeasureTheory Topology Matrix NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.ModuLR
open scoped NNReal ENNReal TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.addEquivAddHaarChar_prodCongr : ∀ (G₁ G₂ : Type) [AddCommGroup G₁] [TopologicalSpace G₁] [IsTopologicalAddGroup G₁] [LocallyCompactSpace G₁] [T2Space G₁] [SecondCountableTopology G₁] [MeasurableSpace G₁] [BorelSpace G₁] [AddCommGroup G₂] [TopologicalSpace G₂] [IsTopologicalAddGroup G₂] [LocallyCompactSpace G₂] [T2Space G₂] [SecondCountableTopology G₂] [MeasurableSpace G₂] [BorelSpace G₂] (e₁ : G₁ ≃ₜ+ G₁) (e₂ : G₂ ≃ₜ+ G₂), addEquivAddHaarChar (prodCE e₁ e₂) = addEquivAddHaarChar e₁ * addEquivAddHaarChar e₂ := by
  first | exact @GlobalTheory.ModuLR.addEquivAddHaarChar_prodCE | exact GlobalTheory.ModuLR.addEquivAddHaarChar_prodCE | (intros; apply GlobalTheory.ModuLR.addEquivAddHaarChar_prodCE <;> assumption)
