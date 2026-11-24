module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryMovingUnitVector
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FreeCell
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HypOneZeroZero
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import Init.Core
public import Init.Data.Fin.Basic
public import Init.Data.Nat.Basic
public import Init.Data.NeZero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypStage
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_moving_unit_vector : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] (x : Fin (M + 2) → R ⊗[F] E), IsUnit (x 0) → ∃ g : HA R σ (hypOne J), ∀ v : Fin (M + 2) → R ⊗[F] E, ((HA.mat R σ (hypOne J) g : GL (Fin (M + 2)) (R ⊗[F] E)) : Matrix (Fin (M + 2)) (Fin (M + 2)) (R ⊗[F] E)).mulVec v = cvec R σ J x v := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.HypUnit.cvec_unitary | exact GlobalTheory.CompanionTheory.WeilSiegel.HypUnit.cvec_unitary | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.HypUnit.cvec_unitary <;> assumption)
