module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdelicBoxCompact
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RatVInjective
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ZeroMemBoxF
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Topology.Defs.Filter

@[expose] public section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov GlobalTheory.CompanionTheory.RedCov.Simple
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelic_box_compact : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], IsCompact (boxF F 1) ∧ IsCompact (boxE F E 1) := by
  first | exact @GlobalTheory.CompanionTheory.RedCov.Simple.BoxCpt.main | exact GlobalTheory.CompanionTheory.RedCov.Simple.BoxCpt.main | (intros; apply GlobalTheory.CompanionTheory.RedCov.Simple.BoxCpt.main <;> assumption)
