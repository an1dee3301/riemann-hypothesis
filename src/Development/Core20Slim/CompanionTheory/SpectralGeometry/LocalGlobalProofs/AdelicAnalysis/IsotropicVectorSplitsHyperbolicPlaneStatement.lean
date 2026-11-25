module

public import Mathlib
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.IsotropicVectorSplitsHyperbolicPlane
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.HypJ
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.NumberTheory.NumberField.Basic

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isotropic_vector_splits_hyperbolic_plane : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ x : Fin M → E, x ≠ 0 → hE σ J x x = 0 → ∃ (M₁ : ℕ) (hM : M = M₁ + 2) (g : GL (Fin (M₁ + 2)) E) (J₁ : Matrix (Fin M₁) (Fin M₁) E), IsHermND σ J₁ ∧ hypJ J₁ = cT (σ : E →+* E) (g : Matrix (Fin (M₁ + 2)) (Fin (M₁ + 2)) E) * (hM ▸ J) * (g : Matrix (Fin (M₁ + 2)) (Fin (M₁ + 2)) E) := by
  first | exact @GlobalTheory.CompanionTheory.SW.HypSplit.splitHyp | exact GlobalTheory.CompanionTheory.SW.HypSplit.splitHyp | (intros; apply GlobalTheory.CompanionTheory.SW.HypSplit.splitHyp <;> assumption)
