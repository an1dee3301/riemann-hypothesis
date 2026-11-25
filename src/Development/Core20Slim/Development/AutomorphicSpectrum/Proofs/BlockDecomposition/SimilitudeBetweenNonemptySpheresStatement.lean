module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SimilitudeBetweenNonemptySpheres
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BinaryMassMeans.MeanVal
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SiegelWeilMeasureOfCongruentForm
public import Development.Core20Slim.Development.WeilBound.CoreStatements.ThetaDilations.ThetaLint
public import Development.Core20Slim.Development.WeilBound.CoreStatements.ThetaDilations.SdTransport
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.NumberTheory.NumberField.Basic

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.similitude_between_nonempty_spheres : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ J : Matrix (Fin 2) (Fin 2) E, IsHermND σ J → ∀ β β' : F, β ≠ 0 → β' ≠ 0 → (PositivityTheory.Rg.Mass.sph σ J β).Nonempty → (PositivityTheory.Rg.Mass.sph σ J β').Nonempty → ∃ γ : GL (Fin 2) E, cT (σ : E →+* E) (γ : Matrix (Fin 2) (Fin 2) E) * J * (γ : Matrix (Fin 2) (Fin 2) E) = (algebraMap F E (β' / β)) • J := by
  first | exact @GlobalTheory.CompanionTheory.SimilExists.exists_similitude | exact GlobalTheory.CompanionTheory.SimilExists.exists_similitude | (intros; apply GlobalTheory.CompanionTheory.SimilExists.exists_similitude <;> assumption)
