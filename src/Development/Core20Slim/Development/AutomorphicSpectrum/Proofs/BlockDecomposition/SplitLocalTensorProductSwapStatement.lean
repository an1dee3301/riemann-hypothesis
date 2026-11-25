module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitLocalTensorProductSwap
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsHermRingRat
public import Development.AbelianVarietyTheory.Definitions.Foundations.NonemptyAlgHomOfNotIsField
public import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Core
public import Init.Data.Prod
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.IsField
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring

@[expose] public section

open NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.KFin
open Formalism.UG (cT)
open scoped TensorProduct NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_local_tensor_product_swap : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}, IsCMExt F E σ → ∀ (v : HeightOneSpectrum (𝓞 F)), ¬ IsField (Fv F v ⊗[F] E) → ∃ φ : (Fv F v ⊗[F] E) ≃+* Fv F v × Fv F v, (∀ r, φ (sigR (Fv F v) σ r) = (φ r).swap) ∧ ∀ r, r ∈ intLoc F E v ↔ (φ r).1 ∈ v.adicCompletionIntegers F ∧ (φ r).2 ∈ v.adicCompletionIntegers F := by
  first | exact @GlobalTheory.CompanionTheory.KFin.SplitBase.exists_split_ringEquiv | exact GlobalTheory.CompanionTheory.KFin.SplitBase.exists_split_ringEquiv | (intros; apply GlobalTheory.CompanionTheory.KFin.SplitBase.exists_split_ringEquiv <;> assumption)
