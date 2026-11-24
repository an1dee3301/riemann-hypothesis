module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ChainMatrices
public import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.PosIndexMapEqCardOfCongrDiagonal
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.SatakeDualWeyl.Statement
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Fin.Basic
public import Init.Data.Int.Basic
public import Init.Data.Int.Lemmas
public import Init.Data.Int.Order
public import Init.Data.Nat.Basic
public import Init.Data.Nat.Lemmas
public import Init.Data.Sum.Basic
public import Init.Data.Zero
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Submodule.LinearMap
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Finsupp.SMul
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Block
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.LinearAlgebra.SesquilinearForm.Basic
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Logic.Equiv.Sum
public import Mathlib.Logic.Function.CompTypeclasses
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FrameComplement

private theorem cT_sig_eq_conjTranspose {m k : Type} (M : Matrix m k ℂ) :
    Formalism.UG.cT (starRingEnd ℂ) M = Mᴴ := by
  ext i j
  simp [Formalism.UG.cT, Matrix.conjTranspose_apply]

private theorem conjTranspose_submatrix_mul_mul_submatrix {R k l m : Type} [CommRing R] [StarRing R] [Fintype k]
    (B : Matrix k l R) (M : Matrix k k R) (f : m → l) :
    (B.submatrix id f)ᴴ * M * B.submatrix id f = (Bᴴ * M * B).submatrix f f := by
  ext i j
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply]

private theorem Jpq_det_ne_zero (p q : ℕ) : (Formalism.UG.Jpq p q).det ≠ 0 := by
  unfold Formalism.UG.Jpq
  rw [Matrix.det_fromBlocks_zero₂₁]
  simp [Matrix.det_neg]

private theorem conjTranspose_submatrix_mul_reindex_mul_submatrix {n k : Type} [Fintype n] [Fintype k] (e : n ≃ k)
    (Q : Matrix n k ℂ) (J : Matrix n n ℂ) :
    (Q.submatrix e.symm id)ᴴ * J.reindex e e * Q.submatrix e.symm id = Qᴴ * J * Q := by
  rw [Matrix.reindex_apply, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
    Matrix.submatrix_mul_equiv, Matrix.submatrix_id_id]

theorem hasSignature_of_frame {n : Type} [Fintype n] [DecidableEq n] {J : Matrix n n ℂ} {p q : ℕ}
    (hn : Fintype.card n = p + q) (Q : Matrix n (Fin p ⊕ Fin q) ℂ) (hQ : Qᴴ * J * Q = Formalism.UG.Jpq p q) :
    Formalism.UG.HasSignature J p q := by
  classical
  have hc : Fintype.card n = Fintype.card (Fin p ⊕ Fin q) := by simp [hn]
  obtain ⟨e⟩ : Nonempty (n ≃ Fin p ⊕ Fin q) := ⟨Fintype.equivOfCardEq hc⟩
  have hP := conjTranspose_submatrix_mul_reindex_mul_submatrix e Q J
  rw [hQ] at hP
  have hdet : (Q.submatrix e.symm id).det ≠ 0 := by
    intro h0
    apply Jpq_det_ne_zero p q
    rw [← hP, Matrix.det_mul, Matrix.det_mul, h0, mul_zero]
  have hu : IsUnit (Q.submatrix e.symm id) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)
  refine ⟨e, hu.unit, ?_⟩
  rw [IsUnit.unit_spec, cT_sig_eq_conjTranspose]
  exact hP

private theorem card_eq_add_and_exists_conj_eq_Jpq_of_hasSignature {n : Type} [Fintype n] [DecidableEq n] {J : Matrix n n ℂ} {p q : ℕ}
    (h : Formalism.UG.HasSignature J p q) :
    Fintype.card n = p + q ∧ ∃ Q : Matrix n (Fin p ⊕ Fin q) ℂ, Qᴴ * J * Q = Formalism.UG.Jpq p q := by
  obtain ⟨e, P, hP⟩ := h
  refine ⟨by simpa using Fintype.card_congr e, (P : Matrix _ _ ℂ).submatrix e id, ?_⟩
  rw [cT_sig_eq_conjTranspose] at hP
  rw [← hP, ← conjTranspose_submatrix_mul_reindex_mul_submatrix e ((P : Matrix _ _ ℂ).submatrix e id) J]
  simp

private theorem Jpq_eq_diagonal_elim_one_neg_one (p q : ℕ) :
    Formalism.UG.Jpq p q = Matrix.diagonal (Sum.elim (fun _ => (1 : ℂ)) (fun _ => -1)) := by
  ext (i|i) (j|j)
  · by_cases h : i = j <;> simp [Formalism.UG.Jpq, Matrix.diagonal_apply, Matrix.one_apply, h]
  · simp [Formalism.UG.Jpq]
  · simp [Formalism.UG.Jpq]
  · by_cases h : i = j <;> simp [Formalism.UG.Jpq, Matrix.diagonal_apply, Matrix.one_apply, h]

theorem hasSignature_fromBlocks {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    {G : Matrix n n ℂ} {H : Matrix m m ℂ} {p q p' q' : ℕ}
    (hG : Formalism.UG.HasSignature G p q) (hH : Formalism.UG.HasSignature H p' q') :
    Formalism.UG.HasSignature (fromBlocks G 0 0 H) (p + p') (q + q') := by
  classical
  obtain ⟨hn, Q1, hQ1⟩ := card_eq_add_and_exists_conj_eq_Jpq_of_hasSignature hG
  obtain ⟨hm, Q2, hQ2⟩ := card_eq_add_and_exists_conj_eq_Jpq_of_hasSignature hH
  obtain ⟨σ, hσ⟩ : ∃ σ : (Fin p ⊕ Fin q) ⊕ (Fin p' ⊕ Fin q') ≃ Fin (p + p') ⊕ Fin (q + q'),
      σ = (Equiv.sumSumSumComm _ _ _ _).trans (Equiv.sumCongr finSumFinEquiv finSumFinEquiv) :=
    ⟨_, rfl⟩
  apply hasSignature_of_frame (by rw [Fintype.card_sum, hn, hm]; omega)
    ((Matrix.fromBlocks Q1 0 0 Q2).submatrix id σ.symm)
  rw [conjTranspose_submatrix_mul_mul_submatrix, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_multiply]
  simp only [Matrix.conjTranspose_zero, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, hQ1, hQ2]
  rw [Jpq_eq_diagonal_elim_one_neg_one, Jpq_eq_diagonal_elim_one_neg_one, Jpq_eq_diagonal_elim_one_neg_one, Matrix.fromBlocks_diagonal,
    Matrix.submatrix_diagonal_equiv]
  congr 1
  funext x
  obtain ⟨y, rfl⟩ := σ.surjective x
  rcases y with (a|a)|(a|a) <;> simp [hσ]

section

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem gram_det_ne (S : Formalism.BasicNotions.HSpace E) : S.gram.det ≠ 0 := by
  classical
  intro h0
  obtain ⟨c, hc0, hc⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
  have h1 : ∀ i, S.hT (S.frame i) (∑ j, c j • S.frame j) = 0 := by
    intro i
    have h2 := congrFun hc i
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply, Formalism.BasicNotions.HSpace.gram] at h2
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← h2, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, smul_eq_mul, mul_comm]
  have hy : ∀ x, S.hT x (∑ j, c j • S.frame j) = 0 := by
    intro x
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← S.frame.sum_repr x, map_sum S.hT, LinearMap.sum_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [map_smulₛₗ, LinearMap.smul_apply, h1, smul_zero]
  have hy0 := S.nondeg.2 _ hy
  exact hc0 (funext (Fintype.linearIndependent_iff.mp S.frame.linearIndependent c hy0))









end


end GlobalTheory.FrameComplement
