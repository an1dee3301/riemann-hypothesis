module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FlagMeasures.ProdPartialZpow
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PosPartUnitaryMul
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Fin.Basic
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.GroupWithZero.Units.Lemmas
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.Matrix.LDL
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Complex.BigOperators
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fin.SuccPred
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Fin.Basic
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.Order.OrderDual
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

open Matrix Finset Formalism.MainNotions.S
open scoped ComplexOrder

namespace GlobalTheory.Dec

private lemma blockTriangular_toDual_of_isLo {n : ℕ} {b : Matrix (Fin n) (Fin n) ℂ} (hb : IsLo b) :
    b.BlockTriangular OrderDual.toDual :=
  fun i j hij => hb i j (OrderDual.toDual_lt_toDual.mp hij)

private lemma isLo_of_blockTriangular_toDual {n : ℕ} {b : Matrix (Fin n) (Fin n) ℂ}
    (hb : b.BlockTriangular OrderDual.toDual) : IsLo b :=
  fun _ _ hij => hb (OrderDual.toDual_lt_toDual.mpr hij)

theorem exists_isLo_mul_conjTranspose {n : ℕ} {x : Matrix (Fin n) (Fin n) ℂ} (hx : x.PosDef) :
    ∃ b : Matrix (Fin n) (Fin n) ℂ, IsLo b ∧ x = b * bᴴ := by
  classical

  have hLi : (LDL.lowerInv hx).BlockTriangular OrderDual.toDual :=
    LDL.isLowerTriangular_lowerInv hx
  have hL : (LDL.lower hx).BlockTriangular OrderDual.toDual :=
    Matrix.blockTriangular_inv_of_blockTriangular hLi

  have hD : (LDL.diag hx).PosDef := by
    rw [LDL.diag_eq_lowerInv_conj]
    refine hx.mul_mul_conjTranspose_same ?_
    intro v w hvw
    have h := congrArg (fun u => u ᵥ* (LDL.lowerInv hx)⁻¹) hvw
    simpa [Matrix.vecMul_vecMul, Matrix.mul_inv_of_invertible] using h
  have hd : ∀ i, 0 < LDL.diagEntries hx i := fun i => by
    simpa [LDL.diag] using hD.diag_pos (i := i)
  let s : Fin n → ℂ := fun i => ((Real.sqrt (LDL.diagEntries hx i).re : ℝ) : ℂ)
  have hs : ∀ i, s i * star (s i) = LDL.diagEntries hx i := fun i => by
    obtain ⟨hre, him⟩ := Complex.pos_iff.mp (hd i)
    have hsq := Real.mul_self_sqrt hre.le
    apply Complex.ext
    · simp [s, Complex.mul_re, hsq]
    · simp [s, Complex.mul_im, ← him]
  refine ⟨LDL.lower hx * Matrix.diagonal s,
    isLo_of_blockTriangular_toDual (hL.mul (Matrix.blockTriangular_diagonal s)), ?_⟩
  have hDs : LDL.diag hx = Matrix.diagonal s * (Matrix.diagonal s)ᴴ := by
    rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
    unfold LDL.diag
    congr 1
    funext i
    exact (hs i).symm
  conv_lhs => rw [← LDL.lower_conj_diag hx, hDs]
  simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]

theorem one_mem_Omega_leadMinor (n : ℕ) : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ Omega n := by
  intro i
  simp [leadMinor, Matrix.submatrix_one _ (Fin.castLE_injective _)]

theorem diag_ne_zero_of_posDef_mul_conjTranspose {n : ℕ} {b : Matrix (Fin n) (Fin n) ℂ} (hb : IsLo b)
    (hx : (b * bᴴ).PosDef) (l : Fin n) : b l l ≠ 0 := by
  classical
  have hdet : (b * bᴴ).det ≠ 0 := hx.det_pos.ne'
  have hb' : b.det ≠ 0 := fun h => hdet (by rw [Matrix.det_mul, h, zero_mul])
  rw [Matrix.det_of_isLowerTriangular b (blockTriangular_toDual_of_isLo hb)] at hb'
  exact Finset.prod_ne_zero_iff.mp hb' l (Finset.mem_univ l)

private lemma phi_mul_conjTranspose_of_isLo (hT : PhiTri) {n : ℕ} (lam : Fin n → ℝ)
    {b : Matrix (Fin n) (Fin n) ℂ} (hb : IsLo b) (hd : ∀ l, b l l ≠ 0) :
    b * bᴴ ∈ Omega n ∧ Phi lam (b * bᴴ) = ((∏ l, ‖b l l‖ ^ (-(2 * muInt lam l)) : ℝ) : ℂ) := by
  have hup : IsUp bᴴ := fun i j hji => by
    simp [Matrix.conjTranspose_apply, hb j i hji]
  have h := hT n lam b 1 bᴴ hb hup
    (fun l => ⟨hd l, by simpa [Matrix.conjTranspose_apply] using hd l⟩) (one_mem_Omega_leadMinor n)
  rw [Matrix.mul_one] at h
  refine ⟨h.1, ?_⟩
  rw [h.2, Phi_at_one, mul_one, Complex.ofReal_prod]
  refine Finset.prod_congr rfl fun l _ => ?_
  rw [Matrix.conjTranspose_apply, Complex.star_def, Complex.mul_conj', Complex.ofReal_zpow,
    ← zpow_natCast, ← _root_.zpow_mul]
  congr 1
  push_cast
  ring

theorem phiPos_of_phiTri (hT : PhiTri) : PhiPos := by
  intro n lam x hx
  obtain ⟨b, hb, rfl⟩ := exists_isLo_mul_conjTranspose hx
  have hd := fun l => diag_ne_zero_of_posDef_mul_conjTranspose hb hx l
  obtain ⟨hΩ, hΦ⟩ := phi_mul_conjTranspose_of_isLo hT lam hb hd
  refine ⟨hΩ, ?_, ⟨b, hb, rfl⟩, fun b' hb' hx' => ?_⟩
  · rw [hΦ, Complex.zero_lt_real]
    exact Finset.prod_pos fun l _ => zpow_pos (norm_pos_iff.mpr (hd l)) _
  · have hx2 : (b' * b'ᴴ).PosDef := hx' ▸ hx
    rw [hx']
    exact (phi_mul_conjTranspose_of_isLo hT lam hb'
      (fun l => diag_ne_zero_of_posDef_mul_conjTranspose hb' hx2 l)).2

theorem phiPos : PhiPos := phiPos_of_phiTri GlobalTheory.PhiTriangular.phiTri

end GlobalTheory.Dec
