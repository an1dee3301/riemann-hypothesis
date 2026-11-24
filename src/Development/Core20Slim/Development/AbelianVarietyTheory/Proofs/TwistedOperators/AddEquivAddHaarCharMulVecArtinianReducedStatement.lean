module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.AddEquivAddHaarCharMulVecArtinianReduced
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.MulVecCEApply
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
public import Init.Prelude
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.Haar.MulEquivHaarChar
public import Mathlib.RingTheory.Artinian.Defs
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Separation.Hausdorff

@[expose] public section

open MeasureTheory Topology Matrix NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.ModuLR
open scoped NNReal ENNReal TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.addEquivAddHaarChar_mulVec_artinian_reduced : ∀ (B : Type) [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [LocallyCompactSpace B] [T2Space B] [SecondCountableTopology B] [MeasurableSpace B] [BorelSpace B], IsArtinianRing B → IsReduced B → ∀ (κ : Type) [Fintype κ] [DecidableEq κ] [MeasurableSpace (κ → B)] [BorelSpace (κ → B)] (M : Matrix κ κ B) (hM : IsUnit M.det), addEquivAddHaarChar (mulVecCE M hM) = modu B M.det := by
  first | exact @GlobalTheory.ModuArtin.addEquivAddHaarChar_mulVecCE | exact GlobalTheory.ModuArtin.addEquivAddHaarChar_mulVecCE | (intros; apply GlobalTheory.ModuArtin.addEquivAddHaarChar_mulVecCE <;> assumption)
