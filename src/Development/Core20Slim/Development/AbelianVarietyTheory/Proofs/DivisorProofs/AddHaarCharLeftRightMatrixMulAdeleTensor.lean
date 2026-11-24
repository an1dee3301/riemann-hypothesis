module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.MulVecCEApply
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRestrictScalarsMatrixLeftRightMulAdeleTens
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralCompGlInvHaar
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModulusOfNormEqAbs
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarScalingNormAdditive
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalToGlobal.GlobalTheory.GL1.CompactFixesLattice.CompactFixesLattice
public import Formalism.LocalToGlobal.IndefiniteReal.PHeisFC
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.Core20Slim.GroundTheory.GlobalFields.IdeleGroups.IdeleNorms
public import Development.Core20Slim.GroundTheory.GlobalFields.IdeleGroups.InfiniteProjInfiniteEmbeddingOfNe
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Algebra.GroupWithZero.Action.Units
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Order.Positive.Ring
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Basic.Countable.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.Haar.DistribChar
public import Mathlib.MeasureTheory.Measure.Haar.MulEquivHaarChar
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Norm.Defs
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.Algebra.ConstMulAction
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Instances.Matrix

@[expose] public section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet  
open GlobalTheory.Doubling (absE)
open Formalism.UG (cT bc)

noncomputable section
namespace GlobalTheory.ResidueEisenstein.ModMat

theorem addEquivAddHaarChar_lrCE : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (j m : ℕ) [LocallyCompactSpace (Matrix (Fin j) (Fin m) (AF F ⊗[F] E))] [SecondCountableTopology (Matrix (Fin j) (Fin m) (AF F ⊗[F] E))] [MeasurableSpace (Matrix (Fin j) (Fin m) (AF F ⊗[F] E))] [BorelSpace (Matrix (Fin j) (Fin m) (AF F ⊗[F] E))] (g : GL (Fin j) (AF F ⊗[F] E)) (a : GL (Fin m) (AF F ⊗[F] E)), addEquivAddHaarChar (GlobalTheory.ModuLR.lrCE g a) = absE F E (Matrix.GeneralLinearGroup.det g) ^ m * absE F E (Matrix.GeneralLinearGroup.det a) ^ j := by
  intro F E _ _ _ _ _ σ _ j m _ _ _ _ g a
  obtain ⟨κ, _, _, Λ, hΛ, hdet, hchar⟩ := GlobalTheory.ModuLR.exists_matrix_restrictScalars_lrCE F E j m g a
  rw [hchar, GlobalTheory.SiegelCov.addEquivAddHaarChar_mulVecCE_adele]
  have hu : hΛ.unit = Units.map (Algebra.norm (AF F) : AF F ⊗[F] E →* AF F)
      (Matrix.GeneralLinearGroup.det g ^ m * Matrix.GeneralLinearGroup.det a ^ j) := by
    ext
    simp [hdet]
  rw [hu]
  apply NNReal.eq
  rw [GlobalTheory.ModuAdele.distribHaarChar_adeleRing, GlobalTheory.NormScaleHaar.ideleModule_norm, map_mul, map_pow, map_pow]

end GlobalTheory.ResidueEisenstein.ModMat
