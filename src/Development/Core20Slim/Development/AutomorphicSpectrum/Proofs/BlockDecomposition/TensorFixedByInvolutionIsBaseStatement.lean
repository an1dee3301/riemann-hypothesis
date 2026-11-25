module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TensorFixedByInvolutionIsBase
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsHermRingRat
public import Development.AbelianVarietyTheory.Definitions.Foundations.NonemptyAlgHomOfNotIsField
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Core
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

open NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.KFin
open Formalism.UG (cT)
open scoped TensorProduct NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensor_fixed_by_involution_is_base : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}, IsCMExt F E σ → ∀ (K : Type) [Field K] [Algebra F K] (a : K ⊗[F] E), sigR K σ a = a → ∃ x : K, algebraMap K (K ⊗[F] E) x = a := by
  first | exact @GlobalTheory.CompanionTheory.KFin.sigR_fixed_eq_algebraMap | exact GlobalTheory.CompanionTheory.KFin.sigR_fixed_eq_algebraMap | (intros; apply GlobalTheory.CompanionTheory.KFin.sigR_fixed_eq_algebraMap <;> assumption)
