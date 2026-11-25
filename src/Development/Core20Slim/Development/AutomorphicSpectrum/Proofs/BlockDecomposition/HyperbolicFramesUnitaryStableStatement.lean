module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HyperbolicFramesUnitaryStable
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ActWOneApply
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HaarFundamentalDomainOrthogonalSum
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HypOneZeroZero
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCovolOne
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TrMMemFramesEIff
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.NumberTheory.NumberField.Basic

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Unf
open GlobalTheory.CompanionTheory.SW.ThetaStage
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hyperbolic_frames_unitary_stable : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → IsHermND σ (hypOne J) ∧ e0 E M ∈ framesE σ (hypOne J) (0 : Matrix (Fin 1) (Fin 1) E) ∧ ∀ (g : UJ (σ : E →+* E) (hypOne J)) (q : Fin 1 → Fin (M + 2) → E), q ∈ framesE σ (hypOne J) (0 : Matrix (Fin 1) (Fin 1) E) → gact σ g q ∈ framesE σ (hypOne J) (0 : Matrix (Fin 1) (Fin 1) E) := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Unf.Basic.hypOne_basic | exact GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Unf.Basic.hypOne_basic | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Unf.Basic.hypOne_basic <;> assumption)
