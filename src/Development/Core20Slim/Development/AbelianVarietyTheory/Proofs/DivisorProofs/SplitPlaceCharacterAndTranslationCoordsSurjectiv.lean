module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocIsoRefl
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitPlaceAdelicMatrixGivenComponents
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitDetGramOfHermitianSelfDualLatticeSpace
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE absEv unitFin ideleAt)

namespace GlobalTheory.FlipOnto

theorem det_ne_zero_of_isSkew {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {B : Base F E} {n r s : ℕ} {X : Spc F E n} (hX : X.IsSkew σ B r s) : X.J.det ≠ 0 := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have h := GlobalTheory.det_ne_zero_of_hasSig (hX.sig w)
  rw [Matrix.det_smul, ← RingHom.mapMatrix_apply, ← RingHom.map_det] at h
  intro h0
  exact h (by rw [h0, map_zero, mul_zero])

theorem det_ne_zero_of_isHerm {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {B : Base F E} {n r s : ℕ} {X : Spc F E n} (hX : X.IsHerm σ B r s) : X.J.det ≠ 0 := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have h := GlobalTheory.det_ne_zero_of_hasSig (hX.sig w)
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det] at h
  intro h0
  exact h (by rw [h0, map_zero])

theorem isUnit_det_map {F E K : Type} [Field F] [Field E] [Field K] [Algebra F E] [Algebra F K] (t : E →ₐ[F] K)
    {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (hJ : J.det ≠ 0) : IsUnit (J.map t).det := by
  have : (J.map t).det = t J.det := by
    rw [← AlgHom.coe_toRingHom, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  rw [this, isUnit_iff_ne_zero]
  exact (map_ne_zero_iff _ t.toRingHom.injective).mpr hJ

theorem coX_coY_onto : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (n d r s r' s' : ℕ) (X : Spc F E n) (W : Spc F E d), X.IsHerm σ B r s → W.IsSkew σ B r' s' →
    ∀ (v : Pl (F := F)) (t : E →ₐ[F] Fv F v) (bb : GL (Fin n) (Fv F v)) (cc : GL (Fin d) (Fv F v)) (Z : Matrix (Fin n) (Fin d) (Fv F v)),
    (∃ z : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evFin F v) z ∧ z.map (piW (t.comp σ)) = 0 ∧ GlobalTheory.FlipMatch.coX t bb cc z = Z) ∧
    (∃ z : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evFin F v) z ∧ z.map (piW t) = 0 ∧ GlobalTheory.FlipMatch.coY σ X W t bb cc z = Z) := by
  intro F E _ _ _ _ _ σ B hB n d r s r' s' X W hX hW v t bb cc Z
  constructor
  · obtain ⟨u, hu, h0, h1⟩ := GlobalTheory.SplitComps.exists_mat_comps hB.cm v t (bb.1 * Z * cc.1ᵀ) 0
    refine ⟨u, hu, h1, ?_⟩
    have hc : cc.1ᵀ * (cc⁻¹).1ᵀ = 1 := by
      rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]
    unfold GlobalTheory.FlipMatch.coX
    rw [h0, Matrix.mul_assoc, Matrix.mul_assoc, hc, Matrix.mul_one, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
  · have hA : IsUnit (bb.1ᵀ * X.J.map t).det := by
      rw [Matrix.det_mul, Matrix.det_transpose]
      exact (Units.isUnit (Matrix.GeneralLinearGroup.det bb)).mul (isUnit_det_map t (det_ne_zero_of_isHerm hX))
    have hC : IsUnit ((W.J.map t)ᵀ * cc.1).det := by
      rw [Matrix.det_mul, Matrix.det_transpose]
      exact (isUnit_det_map t (det_ne_zero_of_isSkew hW)).mul (Units.isUnit (Matrix.GeneralLinearGroup.det cc))
    obtain ⟨u, hu, h0, h1⟩ := GlobalTheory.SplitComps.exists_mat_comps hB.cm v t 0
      (-((bb.1ᵀ * X.J.map t)⁻¹ * Z * ((W.J.map t)ᵀ * cc.1)⁻¹))
    refine ⟨u, hu, h0, ?_⟩
    unfold GlobalTheory.FlipMatch.coY
    rw [h1]
    calc -(bb.1ᵀ * X.J.map t * -((bb.1ᵀ * X.J.map t)⁻¹ * Z * ((W.J.map t)ᵀ * cc.1)⁻¹) * (W.J.map t)ᵀ * cc.1)
        = (bb.1ᵀ * X.J.map t * (bb.1ᵀ * X.J.map t)⁻¹) * Z * (((W.J.map t)ᵀ * cc.1)⁻¹ * ((W.J.map t)ᵀ * cc.1)) := by
          simp only [Matrix.mul_neg, Matrix.neg_mul, neg_neg, Matrix.mul_assoc]
      _ = Z := by
          rw [Matrix.mul_nonsing_inv _ hA, Matrix.nonsing_inv_mul _ hC, Matrix.one_mul, Matrix.mul_one]

end GlobalTheory.FlipOnto
