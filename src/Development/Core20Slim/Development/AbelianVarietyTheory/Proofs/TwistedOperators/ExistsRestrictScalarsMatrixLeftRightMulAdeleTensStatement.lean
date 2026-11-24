module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRestrictScalarsMatrixLeftRightMulAdeleTens
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.MulVecCEApply
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Core
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Basic.Countable.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.NNReal.Defs
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
public import Mathlib.MeasureTheory.Measure.Haar.MulEquivHaarChar
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Norm.Defs
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Instances.Matrix

@[expose] public section

open MeasureTheory Topology Matrix NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.ModuLR
open scoped NNReal ENNReal TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_restrictScalars_matrix_leftRightMul_adeleTensor : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (m n : ℕ) [LocallyCompactSpace (Matrix (Fin m) (Fin n) (AF F ⊗[F] E))] [SecondCountableTopology (Matrix (Fin m) (Fin n) (AF F ⊗[F] E))] [MeasurableSpace (Matrix (Fin m) (Fin n) (AF F ⊗[F] E))] [BorelSpace (Matrix (Fin m) (Fin n) (AF F ⊗[F] E))] (g : GL (Fin m) (AF F ⊗[F] E)) (a : GL (Fin n) (AF F ⊗[F] E)), ∃ (κ : Type) (_ : Fintype κ) (_ : DecidableEq κ) (Λ : Matrix κ κ (AF F)) (hΛ : IsUnit Λ.det), Λ.det = Algebra.norm (AF F) ((Matrix.GeneralLinearGroup.det g ^ n * Matrix.GeneralLinearGroup.det a ^ m : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) ∧ addEquivAddHaarChar (lrCE g a) = addEquivAddHaarChar (mulVecCE Λ hΛ) := by
  first | exact @GlobalTheory.ModuLR.exists_matrix_restrictScalars_lrCE | exact GlobalTheory.ModuLR.exists_matrix_restrictScalars_lrCE | (intros; apply GlobalTheory.ModuLR.exists_matrix_restrictScalars_lrCE <;> assumption)
