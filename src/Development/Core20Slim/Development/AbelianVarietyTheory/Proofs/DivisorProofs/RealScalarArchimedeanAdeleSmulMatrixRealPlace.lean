module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsModGrowthExpLeNormInfPow
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.Algebra.Algebra.Prod
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Pi
public import Mathlib.Algebra.Ring.Prod
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.WithAbs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.Normed.Ring.WithAbs
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Maps

@[expose] public section

open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

noncomputable section
namespace GlobalTheory.RealScalar

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem ext_realAd (r : ℝ) (w : InfinitePlace F) :
    InfinitePlace.Completion.extensionEmbedding w (evInf F w (realAd F r)) = (r : ℂ) := by
  set y : mixedEmbedding.mixedSpace F := algebraMap ℝ _ r with hy
  set a := (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm y with ha
  have hev : evInf F w (realAd F r) = a w := rfl
  have hay : InfiniteAdeleRing.ringEquiv_mixedSpace F a = y := by rw [ha]; exact RingEquiv.apply_symm_apply _ _
  rw [InfiniteAdeleRing.ringEquiv_mixedSpace_apply] at hay
  rw [hev]
  rcases w.isReal_or_isComplex with hw | hw
  · have h1 := congrFun (congrArg Prod.fst hay) ⟨w, hw⟩
    simp only [hy] at h1
    rw [← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hw]
    rw [show (InfinitePlace.Completion.extensionEmbeddingOfIsReal hw (a w)) = r from by simpa using h1]
  · have h1 := congrFun (congrArg Prod.snd hay) ⟨w, hw⟩
    simpa [hy] using h1

theorem piInf_algebraMap {w : InfinitePlace F} (τ : EmbOver E w) (x : AF F) :
    piInf τ (algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) x) = InfinitePlace.Completion.extensionEmbedding w (evInf F w x) := by
  change infEmb τ (compInf F E w (x ⊗ₜ[F] (1 : E))) = _
  rw [compInf]
  change infEmb τ ((evInf F w x) ⊗ₜ[F] ((AlgHom.id F E) 1)) = _
  rw [infEmb_tmul]
  simp

theorem piInf_realAd_smul {w : InfinitePlace F} (τ : EmbOver E w) (r : ℝ) (z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) :
    piInf τ (realAd F r • z) = (r : ℂ) * piInf τ z := by
  rw [Algebra.smul_def, map_mul, piInf_algebraMap, ext_realAd]

theorem realAd_smul_map : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {α β : Type}
    (τ : ∀ w : InfinitePlace F, EmbOver E w), IsCMExt F E σ →
    ∀ (u : Matrix α β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (r : ℝ) (w : InfinitePlace F),
      (realAd F r • u).map (piInf (τ w)) = (r : ℂ) • u.map (piInf (τ w)) := by
  intro F E _ _ _ _ _ σ α β τ _ u r w
  ext i j
  simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]
  exact piInf_realAd_smul (τ w) r (u i j)

end GlobalTheory.RealScalar
