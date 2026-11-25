module

public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeil.ArchimedeanSiegelWeil.PlaceIntegrals.ZeroBlockCoefficientRankIncrease
public import Mathlib
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HypOneZeroZero
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TrMMemFramesEIff
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.NumberTheory.NumberField.Basic

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free
theorem _root_.GlobalTheory.T.zero_block_coefficient_rank_increase : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ n : ℕ, 1 ≤ n → 2 * n < M → ∀ (h₀ : ∀ a b : Fin n, σ ((0 : Matrix (Fin n) (Fin n) E) b a) = (0 : Matrix (Fin n) (Fin n) E) a b) (h₁ : ∀ a b : Fin (n + 1), σ ((0 : Matrix (Fin (n + 1)) (Fin (n + 1)) E) b a) = (0 : Matrix (Fin (n + 1)) (Fin (n + 1)) E) a b), (framesE σ J (0 : Matrix (Fin n) (Fin n) E)).Nonempty → SWFree σ J (0 : Matrix (Fin n) (Fin n) E) h₀ → SWFree σ (hypOne J) (0 : Matrix (Fin (n + 1)) (Fin (n + 1)) E) h₁ := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.HypStep.hyp_step | exact GlobalTheory.CompanionTheory.WeilSiegel.HypStep.hyp_step
