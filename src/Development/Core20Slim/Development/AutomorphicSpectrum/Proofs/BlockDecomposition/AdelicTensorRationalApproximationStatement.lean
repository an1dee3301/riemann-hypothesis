module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdelicTensorRationalApproximation
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RatVInjective
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ZeroMemBoxF
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov GlobalTheory.CompanionTheory.RedCov.Simple
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelic_tensor_rational_approximation : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (ε : ℝ), 0 < ε → ∃ N : ℕ, 1 ≤ N ∧ ∀ b : AF F ⊗[F] E, ∃ q : ℕ, 1 ≤ q ∧ q ≤ N ∧ ∃ c : E, (q : AF F ⊗[F] E) * b - inclR (F := F) (AF F) c ∈ boxE F E ε := by
  first | exact @GlobalTheory.CompanionTheory.RedCov.Simple.Dirichlet.dirichlet | exact GlobalTheory.CompanionTheory.RedCov.Simple.Dirichlet.dirichlet | (intros; apply GlobalTheory.CompanionTheory.RedCov.Simple.Dirichlet.dirichlet <;> assumption)
