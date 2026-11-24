module

public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.Core20Slim.Development.WeilBound.ThetaLifts.LatticeBasics.Hypotheses2
public import Formalism.LocalRingCardinality.DataParams₂
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.Columns.AbelianHostFieldConditions
public import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Init.Data.Rat.Basic
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Rat
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Basic.Countable.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Finite
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Group.Units
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Separation.Hausdorff
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

noncomputable section

namespace GlobalTheory.EisBL.AETop

open NumberField IsDedekindDomain Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

instance fdAE : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E

instance modTopAE : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩

instance ringAE : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _

theorem nonempty_homeomorphAE : Nonempty (AE F E ≃ₜ (Fin (Module.finrank F E) → AF F)) :=
  GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)

instance t2AE : T2Space (AE F E) := by
  have := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  obtain ⟨e⟩ := nonempty_homeomorphAE (F := F) (E := E)
  exact e.isEmbedding.t2Space

instance locCompactAE : LocallyCompactSpace (AE F E) := by
  have := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  obtain ⟨e⟩ := nonempty_homeomorphAE (F := F) (E := E)
  exact e.isClosedEmbedding.locallyCompactSpace

instance secondCountableAE : SecondCountableTopology (AE F E) := by
  have := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  obtain ⟨e⟩ := nonempty_homeomorphAE (F := F) (E := E)
  exact e.secondCountableTopology

instance topGrpGL {ι : Type} [Fintype ι] [DecidableEq ι] : IsTopologicalGroup (GL ι (AE F E)) := inferInstance

instance isTopologicalGroup_G2 {σ : E →ₐ[F] E} {n : ℕ} {Y : Spc F E n} : IsTopologicalGroup (G2 σ Y) := inferInstance

end GlobalTheory.EisBL.AETop
