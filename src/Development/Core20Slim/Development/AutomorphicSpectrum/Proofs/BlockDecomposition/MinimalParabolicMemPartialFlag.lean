module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GoodConstOfAniso
public import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactUnipFlag
public import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Classical
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Fin.Basic
public import Init.Data.Fin.Lemmas
public import Init.Data.Int.Basic
public import Init.Data.Int.Lemmas
public import Init.Data.Int.Order
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fin.SuccPred
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Fin.Basic
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RapidDecay
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal Topology

namespace GlobalTheory.CompanionTheory.RapidDecay

theorem mul_firstCols_eq {R : Type} [CommRing R] {n r : ℕ} (M : Matrix (Fin n) (Fin n) R)
    (Z : Matrix (Fin n) (Fin r) R) (B : Matrix (Fin r) (Fin r) R) (hB : B.BlockTriangular id)
    (e : M * Z = Z * B) (s : Fin r) :
    M * Z.submatrix id (Fin.castLE s.2) =
      Z.submatrix id (Fin.castLE s.2) * B.submatrix (Fin.castLE s.2) (Fin.castLE s.2) := by
  ext i j
  have h := congrFun (congrFun e i) (Fin.castLE s.2 j)
  simp only [Matrix.mul_apply, Matrix.submatrix_apply, id_eq] at h ⊢
  rw [h]
  refine (Fintype.sum_of_injective (Fin.castLE s.2) (Fin.castLE_injective s.2) _ _ ?_ ?_).symm
  · intro l hl
    have hlt : Fin.castLE s.2 j < l := by
      by_contra hc
      apply hl
      have hj := j.isLt
      have hc' : l.val ≤ j.val := not_lt.mp hc
      exact ⟨⟨l.val, by omega⟩, Fin.ext rfl⟩
    have h0 : B l (Fin.castLE s.2 j) = 0 := hB hlt
    rw [h0, mul_zero]
  · intro l
    rfl

theorem mem_parFlag_first_of_minParOne : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X : Matrix (Fin n) (Fin r) E), ∀ p ∈ minParOne σ J X, ∀ s : Fin r, p ∈ GlobalTheory.UAut.parFlag σ J (pre X s) fun _ => 0 := by
  intro F E _ _ _ _ _ σ n J r X p hp s
  obtain ⟨B, hB, e, hu⟩ := hp
  choose u hu1 _ using hu
  have e1 := mul_firstCols_eq _ _ B hB e s
  have hBs : (B.submatrix (Fin.castLE s.2) (Fin.castLE s.2)).BlockTriangular id := by
    intro i j hij
    exact hB hij
  have hdet : IsUnit (B.submatrix (Fin.castLE s.2) (Fin.castLE s.2)).det := by
    rw [Matrix.det_of_isUpperTriangular hBs]
    refine ⟨∏ i, u (Fin.castLE s.2 i), ?_⟩
    rw [Units.coe_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Matrix.submatrix_apply, hu1]
  have hZ : GlobalTheory.SiegelSet.adMat F (pre X s) =
      (GlobalTheory.SiegelSet.adMat F X).submatrix id (Fin.castLE s.2) := rfl
  refine ⟨⟨B.submatrix (Fin.castLE s.2) (Fin.castLE s.2), ?_, ?_⟩,
    ⟨(B.submatrix (Fin.castLE s.2) (Fin.castLE s.2))⁻¹, ?_, ?_⟩⟩
  · intro i j h
    exact absurd h (lt_irrefl 0)
  · rw [hZ]
    exact e1
  · intro i j h
    exact absurd h (lt_irrefl 0)
  · rw [hZ, map_inv]
    set g := GlobalTheory.AdelicU.matHom (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) σ J p
    set Z := (GlobalTheory.SiegelSet.adMat F X).submatrix id (Fin.castLE s.2)
    set Bs := B.submatrix (Fin.castLE s.2) (Fin.castLE s.2)
    have h1 : Bs * Bs⁻¹ = 1 := Matrix.mul_nonsing_inv Bs hdet
    have h2 : (g⁻¹).val * g.val = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    calc (g⁻¹).val * Z
        = (g⁻¹).val * Z * (Bs * Bs⁻¹) := by rw [h1, Matrix.mul_one]
      _ = (g⁻¹).val * (g.val * Z) * Bs⁻¹ := by
          rw [e1]
          simp only [Matrix.mul_assoc]
      _ = Z * Bs⁻¹ := by rw [← Matrix.mul_assoc, h2, Matrix.one_mul]

end GlobalTheory.CompanionTheory.RapidDecay

end
