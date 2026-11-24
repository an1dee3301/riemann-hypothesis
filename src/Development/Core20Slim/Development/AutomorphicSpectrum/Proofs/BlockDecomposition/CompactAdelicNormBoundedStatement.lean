module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactAdelicNormBounded
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RatVInjective
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ZeroMemBoxF
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.Core20Slim.GroundTheory.AutomorphicForms.ReductionHeight
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Defs.Filter

@[expose] public section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov GlobalTheory.CompanionTheory.RedCov.Simple
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compact_adelic_norm_bounded : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ) (D : Set (Fin N → AF F)), IsCompact D → ∃ P : ℝ, 0 < P ∧ ∀ y ∈ D, GroundTheory.Automorphic.Reduction.adelicNorm y ≤ P := by
  first | exact @GlobalTheory.CompanionTheory.RedCov.Simple.exists_adelicNorm_le_of_isCompact | exact GlobalTheory.CompanionTheory.RedCov.Simple.exists_adelicNorm_le_of_isCompact | (intros; apply GlobalTheory.CompanionTheory.RedCov.Simple.exists_adelicNorm_le_of_isCompact <;> assumption)
