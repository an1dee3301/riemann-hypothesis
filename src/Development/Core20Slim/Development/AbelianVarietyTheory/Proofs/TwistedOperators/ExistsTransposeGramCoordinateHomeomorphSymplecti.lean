module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsReading
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAddEquivSymplecticCoordsOrientedModel
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Instances.Matrix

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Twist.exists_transposeGram_coordinate_homeomorph_symplectic

variable {D : D7}

theorem gram_map_mul_inv {R : Type*} [CommRing R] (S : HSp D) (φ : D.host.E →+* R) :
    S.gram.map φ * (S.gram⁻¹).map φ = 1 := by
  rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 (GlobalTheory.Twist.exists_addEquiv_symplecticCoords_orientedModel.gram_det_ne_zero S)),
    Matrix.map_one _ φ.map_zero φ.map_one]

theorem gram_inv_map_mul {R : Type*} [CommRing R] (S : HSp D) (φ : D.host.E →+* R) :
    (S.gram⁻¹).map φ * S.gram.map φ = 1 := by
  rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 (GlobalTheory.Twist.exists_addEquiv_symplecticCoords_orientedModel.gram_det_ne_zero S)),
    Matrix.map_one _ φ.map_zero φ.map_one]

def coordsLin (S T S' T' : HSp D) (e₁ : Fin T'.rank ≃ Fin S.rank) (e₂ : Fin S'.rank ≃ Fin T.rank) :
    WO S' T' ≃ₗ[AE D] WO S T where
  toFun u := (HMul.hMul (uᵀ.submatrix e₂.symm e₁.symm) (S.gram.map (incA D)) : Matrix (Fin T.rank) (Fin S.rank) (AE D))
  invFun x := ((HMul.hMul x ((S.gram⁻¹).map (incA D)) : Matrix (Fin T.rank) (Fin S.rank) (AE D))ᵀ).submatrix e₁ e₂
  map_add' u v := by
    show (u + v)ᵀ.submatrix e₂.symm e₁.symm * _ = uᵀ.submatrix e₂.symm e₁.symm * _ + vᵀ.submatrix e₂.symm e₁.symm * _
    rw [Matrix.transpose_add, ← Matrix.add_mul]
    rfl
  map_smul' c u := by
    show (c • u)ᵀ.submatrix e₂.symm e₁.symm * _ = c • (uᵀ.submatrix e₂.symm e₁.symm * _)
    rw [Matrix.transpose_smul, ← Matrix.smul_mul]
    rfl
  left_inv u := by
    show ((uᵀ.submatrix e₂.symm e₁.symm * S.gram.map (incA D) * (S.gram⁻¹).map (incA D))ᵀ).submatrix e₁ e₂ = u
    rw [Matrix.mul_assoc, gram_map_mul_inv, Matrix.mul_one]
    ext i j; simp
  right_inv x := by
    dsimp only
    have : (((HMul.hMul x ((S.gram⁻¹).map (incA D)) : Matrix (Fin T.rank) (Fin S.rank) (AE D))ᵀ).submatrix e₁ e₂)ᵀ.submatrix e₂.symm e₁.symm =
        (HMul.hMul x ((S.gram⁻¹).map (incA D)) : Matrix (Fin T.rank) (Fin S.rank) (AE D)) := by
      ext i j; simp
    rw [this, Matrix.mul_assoc, gram_inv_map_mul, Matrix.mul_one]

theorem map_transpose_submatrix {A B : Type*} [Semiring A] [Semiring B] (φ : A →+* B) {m n p q : Type*}
    (u : Matrix m n A) (f : p → n) (g : q → m) : (uᵀ.submatrix f g).map φ = ((u.map φ)ᵀ).submatrix f g := rfl

theorem coordsLin_map_zero {R : Type*} [Semiring R] (φ : AE D →+* R) (S T S' T' : HSp D) (e₁ : Fin T'.rank ≃ Fin S.rank)
    (e₂ : Fin S'.rank ≃ Fin T.rank) (x : WO S' T') (h : x.map φ = 0) : (coordsLin S T S' T' e₁ e₂ x).map φ = 0 := by
  change (HMul.hMul (xᵀ.submatrix e₂.symm e₁.symm) (S.gram.map (incA D)) : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map φ = 0
  rw [Matrix.map_mul, map_transpose_submatrix, h]
  simp

theorem coordsLin_symm_map_zero {R : Type*} [Semiring R] (φ : AE D →+* R) (S T S' T' : HSp D) (e₁ : Fin T'.rank ≃ Fin S.rank)
    (e₂ : Fin S'.rank ≃ Fin T.rank) (y : WO S T) (h : y.map φ = 0) : ((coordsLin S T S' T' e₁ e₂).symm y).map φ = 0 := by
  change (((HMul.hMul y ((S.gram⁻¹).map (incA D)) : Matrix (Fin T.rank) (Fin S.rank) (AE D))ᵀ).submatrix e₁ e₂).map φ = 0
  rw [map_transpose_submatrix, Matrix.map_mul, h]
  simp

theorem coordsLin_map_zero_iff {R : Type*} [Semiring R] (φ : AE D →+* R) (S T S' T' : HSp D) (e₁ : Fin T'.rank ≃ Fin S.rank)
    (e₂ : Fin S'.rank ≃ Fin T.rank) (x : WO S' T') : (coordsLin S T S' T' e₁ e₂ x).map φ = 0 ↔ x.map φ = 0 := by
  refine ⟨fun h => ?_, coordsLin_map_zero φ S T S' T' e₁ e₂ x⟩
  have := coordsLin_symm_map_zero φ S T S' T' e₁ e₂ _ h
  rwa [LinearEquiv.symm_apply_apply] at this

theorem coordsLin_rat_iff (S T S' T' : HSp D) (e₁ : Fin T'.rank ≃ Fin S.rank)
    (e₂ : Fin S'.rank ≃ Fin T.rank) (x : WO S' T') : coordsLin S T S' T' e₁ e₂ x ∈ ratL T S ↔ x ∈ ratL T' S' := by
  constructor
  · rintro ⟨γ, hγ⟩
    refine ⟨((γ * S.gram⁻¹)ᵀ).submatrix e₁ e₂, ?_⟩
    rw [← (coordsLin S T S' T' e₁ e₂).symm_apply_apply x, ← hγ]
    change (((γ * S.gram⁻¹)ᵀ).submatrix e₁ e₂).map (incA D) =
      ((HMul.hMul (γ.map (incA D)) ((S.gram⁻¹).map (incA D)) : Matrix (Fin T.rank) (Fin S.rank) (AE D))ᵀ).submatrix e₁ e₂
    rw [map_transpose_submatrix, Matrix.map_mul]
  · rintro ⟨γ, rfl⟩
    refine ⟨γᵀ.submatrix e₂.symm e₁.symm * S.gram, ?_⟩
    change (γᵀ.submatrix e₂.symm e₁.symm * S.gram).map (incA D) =
      (HMul.hMul ((γ.map (incA D))ᵀ.submatrix e₂.symm e₁.symm) (S.gram.map (incA D)) : Matrix (Fin T.rank) (Fin S.rank) (AE D))
    rw [Matrix.map_mul, map_transpose_submatrix]

theorem coordsLin_spec (D : D7) (S T S' T' : HSp D) (e₁ : Fin T'.rank ≃ Fin S.rank) (e₂ : Fin S'.rank ≃ Fin T.rank) :
    ∃ L : WO S' T' ≃ₗ[AE D] WO S T,
      (∀ u, L u = (HMul.hMul (uᵀ.submatrix e₂.symm e₁.symm) (S.gram.map (incA D)) : Matrix (Fin T.rank) (Fin S.rank) (AE D))) ∧
      (∀ x : Matrix (Fin T.rank) (Fin S.rank) (AE D),
        L.symm x = ((HMul.hMul x ((S.gram⁻¹).map (incA D)) : Matrix (Fin T.rank) (Fin S.rank) (AE D))ᵀ).submatrix e₁ e₂) ∧
      Continuous L ∧ Continuous L.symm ∧ (∀ x, L x ∈ ratL T S ↔ x ∈ ratL T' S') ∧
      (∀ x, (L x).map (infPart D) = 0 ↔ x.map (infPart D) = 0) ∧ ∀ x, (L x).map (finPart D) = 0 ↔ x.map (finPart D) = 0 := by
  refine ⟨coordsLin S T S' T' e₁ e₂, fun _ => rfl, fun _ => rfl, ?_, ?_, coordsLin_rat_iff S T S' T' e₁ e₂,
    coordsLin_map_zero_iff _ S T S' T' e₁ e₂, coordsLin_map_zero_iff _ S T S' T' e₁ e₂⟩
  · change Continuous fun u : WO S' T' =>
      (HMul.hMul (uᵀ.submatrix e₂.symm e₁.symm) (S.gram.map (incA D)) : Matrix (Fin T.rank) (Fin S.rank) (AE D))
    exact (continuous_id.matrix_transpose.matrix_submatrix _ _).matrix_mul continuous_const
  · change Continuous fun x : WO S T =>
      ((HMul.hMul x ((S.gram⁻¹).map (incA D)) : Matrix (Fin T.rank) (Fin S.rank) (AE D))ᵀ).submatrix e₁ e₂
    exact ((continuous_id.matrix_mul continuous_const).matrix_transpose).matrix_submatrix _ _

end GlobalTheory.Twist.exists_transposeGram_coordinate_homeomorph_symplectic
