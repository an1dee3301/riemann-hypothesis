module

public import Mathlib
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.CStarAlgebra.CStarMatrix
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.RMulGram

theorem mul_regroup {A : Type} [CommRing A] {m n : Type} [Fintype m] [Fintype n]
    (P : Matrix n n A) (B : Matrix n m A) (J : Matrix m m A) (C : Matrix m n A)
    (g : Matrix n n A) :
    (P * B) * J * (C * g) = P * ((B * J : Matrix n m A) * C) * g := by
  simp only [Matrix.mul_assoc]

section
variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]

def colsM {M n : ℕ} (X : Fin n → Fin M → R ⊗[F] E) : Matrix (Fin M) (Fin n) (R ⊗[F] E) :=
  fun i a => X a i

theorem colsM_injective {M n : ℕ} {X Y : Fin n → Fin M → R ⊗[F] E}
    (h : colsM R X = colsM R Y) : X = Y := by
  funext a i
  exact congrFun (congrFun h i) a

theorem gramR_eq_mul (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (X : Fin n → Fin M → R ⊗[F] E) :
    gramR R σ J X =
      (cT (sigR R σ) (colsM R X) * JR R J : Matrix (Fin n) (Fin M) (R ⊗[F] E)) * colsM R X := by
  ext a b
  simp only [gramR, hR, hform, Matrix.mul_apply, cT, Matrix.transpose_apply, Matrix.map_apply,
    colsM, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_mul]
  congr 1

theorem colsM_rmul {M n : ℕ} (X : Fin n → Fin M → R ⊗[F] E)
    (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)) :
    colsM R (rmul R X g) = colsM R X * g := by
  ext i a
  simp only [rmul, colsM, Matrix.mul_apply]

theorem gramR_rmul (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (X : Fin n → Fin M → R ⊗[F] E) (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)) :
    gramR R σ J (rmul R X g) = cT (sigR R σ) g * gramR R σ J X * g := by
  rw [gramR_eq_mul, gramR_eq_mul, colsM_rmul, cT_mul]
  exact mul_regroup _ _ _ _ _

theorem rmul_rmul {M n : ℕ} (X : Fin n → Fin M → R ⊗[F] E)
    (g g' : Matrix (Fin n) (Fin n) (R ⊗[F] E)) :
    rmul R (rmul R X g) g' = rmul R X (g * g') := by
  apply colsM_injective
  rw [colsM_rmul, colsM_rmul, colsM_rmul, Matrix.mul_assoc]

theorem rmul_one {M n : ℕ} (X : Fin n → Fin M → R ⊗[F] E) : rmul R X 1 = X := by
  apply colsM_injective
  rw [colsM_rmul, Matrix.mul_one]

theorem actTup_rmul {M n : ℕ} (k : GL (Fin M) (R ⊗[F] E)) (X : Fin n → Fin M → R ⊗[F] E)
    (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)) :
    actTup R k (rmul R X g) = rmul R (actTup R k X) g := by
  funext a i
  simp only [actTup, rmul, Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun j _ => (mul_assoc _ _ _).symm

end

theorem rmul_gram_facts : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] (M n : ℕ) (J : Matrix (Fin M) (Fin M) E) (X : Fin n → Fin M → R ⊗[F] E) (g g' : Matrix (Fin n) (Fin n) (R ⊗[F] E)), gramR R σ J (rmul R X g) = cT (sigR R σ) g * gramR R σ J X * g ∧ rmul R (rmul R X g) g' = rmul R X (g * g') ∧ rmul R X 1 = X ∧ ∀ k : GL (Fin M) (R ⊗[F] E), actTup R k (rmul R X g) = rmul R (actTup R k X) g := by
  intro F E _ _ _ _ _ σ _ R _ _ M n J X g g'
  exact ⟨gramR_rmul R σ J X g, rmul_rmul R X g g', rmul_one R X, fun k => actTup_rmul R k X g⟩

end GlobalTheory.CompanionTheory.SW.RMulGram
