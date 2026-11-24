module

public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GenFinLocB
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.BlockLowerRightMulBlockMatrix
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GenFinLocA
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocRedField
public import Formalism.SatakeDualWeyl.Statement
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Block
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result

@[expose] public section

noncomputable section

open Matrix

namespace PositivityTheory.Rg.Sw.Glob.GenFinLocAH

variable {R : Type} [CommRing R] {n : ℕ}

theorem det_cT (σ : R →+* R) (a : Matrix (Fin n) (Fin n) R) : (Formalism.UG.cT σ a).det = σ a.det := by
  unfold Formalism.UG.cT; rw [det_transpose, det_map]

theorem cT_cT (σ : R →+* R) (hσ : ∀ x, σ (σ x) = x) {m p : Type} (a : Matrix m p R) :
    Formalism.UG.cT σ (Formalism.UG.cT σ a) = a := by
  ext i j; simp [Formalism.UG.cT, hσ]

theorem cT_inv (σ : R →+* R) (a : Matrix (Fin n) (Fin n) R) (ha : IsUnit a.det) :
    Formalism.UG.cT σ a⁻¹ = (Formalism.UG.cT σ a)⁻¹ := by
  unfold Formalism.UG.cT; rw [map_nonsing_inv σ a ha, transpose_nonsing_inv]

theorem uni_levi (σ : R →+* R) (hσ : ∀ x, σ (σ x) = x) (a : Matrix (Fin n) (Fin n) R) (ha : IsUnit a.det) :
    Uni σ (GlobalTheory.StdUnn.blk4 a 0 0 (Formalism.UG.cT σ a)⁻¹) := by
  have hca : IsUnit (Formalism.UG.cT σ a).det := by rw [det_cT]; exact ha.map σ
  apply bf_injective
  unfold J2
  rw [bf_mul, bf_mul, bf_cT, block_matrix_to_fromBlocks, block_matrix_to_fromBlocks, cT_fromBlocks, fromBlocks_multiply, fromBlocks_multiply]
  rw [cT_inv σ _ hca, cT_cT σ hσ]
  have hc0 : Formalism.UG.cT σ (0 : Matrix (Fin n) (Fin n) R) = 0 := by ext; simp [Formalism.UG.cT]
  simp only [hc0, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.mul_neg, Matrix.neg_mul, add_zero,
    zero_add, mul_nonsing_inv _ hca, nonsing_inv_mul _ ha, neg_zero]

theorem eI_mul_eI (I : Finset (Fin n)) : (eI I : Matrix (Fin n) (Fin n) R) * eI I = eI I := by
  unfold eI; rw [diagonal_mul_diagonal]; congr 1; funext i; split_ifs <;> simp

theorem cT_eI (σ : R →+* R) (I : Finset (Fin n)) : Formalism.UG.cT σ (eI I : Matrix (Fin n) (Fin n) R) = eI I := by
  unfold Formalism.UG.cT; rw [eI_map, eI, diagonal_transpose]

theorem uni_wIm (σ : R →+* R) (I : Finset (Fin n)) : Uni σ (wIm I : Matrix (Fin (n + n)) (Fin (n + n)) R) := by
  apply bf_injective
  unfold J2 wIm
  rw [bf_mul, bf_mul, bf_cT, block_matrix_to_fromBlocks, block_matrix_to_fromBlocks, cT_fromBlocks, fromBlocks_multiply, fromBlocks_multiply]
  have h1 : Formalism.UG.cT σ (1 - eI I : Matrix (Fin n) (Fin n) R) = 1 - eI I := by
    unfold Formalism.UG.cT; rw [Matrix.map_sub _ (map_sub σ), Matrix.map_one _ (map_zero σ) (map_one σ), eI_map, transpose_sub,
      transpose_one, eI, diagonal_transpose]
  have h2 : Formalism.UG.cT σ (-eI I : Matrix (Fin n) (Fin n) R) = -eI I := by
    unfold Formalism.UG.cT; rw [Matrix.map_neg _ (map_neg σ), eI_map, transpose_neg, eI, diagonal_transpose]
  rw [h1, h2, cT_eI]
  have hE := eI_mul_eI (R := R) I
  congr 1 <;> simp only [Matrix.mul_zero, Matrix.mul_one, Matrix.mul_neg, Matrix.neg_mul, add_zero,
    zero_add, neg_neg, Matrix.mul_sub, Matrix.sub_mul, Matrix.one_mul, hE] <;> abel_nf

end PositivityTheory.Rg.Sw.Glob.GenFinLocAH
