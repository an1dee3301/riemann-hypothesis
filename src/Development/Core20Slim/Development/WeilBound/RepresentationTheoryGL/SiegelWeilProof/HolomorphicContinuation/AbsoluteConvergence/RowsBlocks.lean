module

public import Mathlib
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.InGBlocks
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.DerivativeVacuumDilationsAlt
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobData
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.IsSingTest
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.GroupWithZero.Units.Lemmas
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Ring.CharZero
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Int.Cast.Lemmas
public import Mathlib.Data.Matrix.Block
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.InvariantBasisNumber
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.RingTheory.FiniteType
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Tactic.Ring.RingNF

@[expose] public section

noncomputable section

open Matrix
open scoped ComplexOrder

namespace PositivityTheory.Rg.Sw.AbsSt

open PositivityTheory.Rg.Sw IwaPf

variable {n : ℕ}

theorem detU1 : CayleyBlocksInvertible := by
  intro n y
  have hg : InG (mR y) := y.2
  refine ⟨det_ne (mR y) hg Complex.I (by norm_num [Complex.ext_iff]), ?_⟩
  show (-(Complex.I • toBlocks₂₁ (mR y)) + toBlocks₂₂ (mR y)).det ≠ 0
  rw [← neg_smul]
  exact det_ne (mR y) hg (-Complex.I) (by norm_num [Complex.ext_iff])

theorem rows_blocks (g : M2 n) (h : InG g) : g.toBlocks₂₁ * g.toBlocks₂₂ᴴ = g.toBlocks₂₂ * g.toBlocks₂₁ᴴ := by
  have hr := inG_rows g h
  rw [← fromBlocks_toBlocks g] at hr
  simp only [JJ, fromBlocks_conjTranspose, fromBlocks_multiply] at hr
  have h22 := congrArg Matrix.toBlocks₂₂ hr
  simp at h22
  exact (neg_add_eq_zero.mp h22).symm

def kmat (U1 U2 : Matrix (Fin n) (Fin n) ℂ) : M2 n :=
  fromBlocks ((1 / 2 : ℂ) • (U1 + U2)) ((Complex.I / 2) • (U1 - U2)) (-((Complex.I / 2) • (U1 - U2)))
    ((1 / 2 : ℂ) • (U1 + U2))

theorem kmat_unit (U1 U2 : Matrix (Fin n) (Fin n) ℂ) (h1 : U1ᴴ * U1 = 1) (h2 : U2ᴴ * U2 = 1) :
    (kmat U1 U2)ᴴ * kmat U1 U2 = 1 := by
  simp only [kmat, fromBlocks_conjTranspose, fromBlocks_multiply, conjTranspose_smul,
    conjTranspose_add, conjTranspose_sub, conjTranspose_neg, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_neg, Matrix.neg_mul, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul, h1, h2]
  simp only [Complex.star_def, map_div₀, map_one, map_ofNat, Complex.conj_I]
  rw [← fromBlocks_one]
  congr 1
  all_goals (match_scalars <;> ring_nf <;> simp only [Complex.I_sq] <;> ring_nf)

theorem kmat_inG (U1 U2 : Matrix (Fin n) (Fin n) ℂ) (h1 : U1ᴴ * U1 = 1) (h2 : U2ᴴ * U2 = 1) : InG (kmat U1 U2) := by
  unfold InG JJ
  simp only [kmat, fromBlocks_conjTranspose, fromBlocks_multiply, conjTranspose_smul,
    conjTranspose_add, conjTranspose_sub, conjTranspose_neg, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_neg, Matrix.neg_mul, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul,
    add_zero, zero_add, neg_neg, h1, h2]
  simp only [Complex.star_def, map_div₀, map_one, map_ofNat, Complex.conj_I]
  congr 1
  all_goals (match_scalars <;> ring_nf <;> simp only [Complex.I_sq] <;> ring_nf)

private theorem mul_inv_mul_proj_of_ker_iff (g : M2 n) (h : InG g) : u1 g * (u1 g)ᴴ = u2 g * (u2 g)ᴴ := by
  have hr := rows_blocks g h
  simp only [u1, u2, conjTranspose_add, conjTranspose_neg, conjTranspose_smul, Matrix.mul_add,
    Matrix.add_mul, Matrix.mul_neg, Matrix.neg_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← hr]
  simp only [Complex.star_def, Complex.conj_I]
  module

private theorem proj_mul_mul_proj_of_ker_iff (U1 U2 : Matrix (Fin n) (Fin n) ℂ) (Y : M2 n) :
    toBlocks₂₁ (Y * (kmat U1 U2)ᴴ) =
      (1 / 2 : ℂ) • (((-Complex.I) • u1 Y) * U1ᴴ + (Complex.I • u2 Y) * U2ᴴ) := by
  rw [← fromBlocks_toBlocks Y]
  simp only [u1, u2, kmat, fromBlocks_conjTranspose, fromBlocks_multiply, toBlocks_fromBlocks₂₁,
    toBlocks_fromBlocks₂₂, conjTranspose_smul, conjTranspose_add, conjTranspose_sub, conjTranspose_neg,
    Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_neg, Matrix.neg_mul,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, smul_add, smul_neg, smul_sub]
  simp only [Complex.star_def, map_div₀, map_one, map_ofNat, Complex.conj_I]
  match_scalars <;> ring_nf <;> simp only [Complex.I_sq] <;> ring_nf

private theorem inv_mul_unitary_of_mul_conjTranspose_eq (a b : Matrix (Fin n) (Fin n) ℂ) (hab : a * aᴴ = b * bᴴ) (h2d : b.det ≠ 0) :
    (b⁻¹ * a) * (b⁻¹ * a)ᴴ = 1 ∧ a * (b⁻¹ * a)ᴴ = b := by
  have hbu : IsUnit b.det := isUnit_iff_ne_zero.mpr h2d
  have hbH : IsUnit bᴴ.det := by
    rw [det_conjTranspose]
    exact isUnit_iff_ne_zero.mpr (star_ne_zero.mpr h2d)
  have haV : a * (b⁻¹ * a)ᴴ = b := by
    rw [conjTranspose_mul, conjTranspose_nonsing_inv, ← Matrix.mul_assoc, hab, Matrix.mul_assoc,
      mul_nonsing_inv _ hbH, Matrix.mul_one]
  refine ⟨?_, haV⟩
  rw [Matrix.mul_assoc, haV, nonsing_inv_mul b hbu]

theorem iwa : Iwa := by
  intro n y
  have hg : InG (mR y) := y.2
  obtain ⟨_, h2d⟩ := detU1 n y
  obtain ⟨hVV, haV⟩ := inv_mul_unitary_of_mul_conjTranspose_eq (u1 (mR y)) (u2 (mR y)) (mul_inv_mul_proj_of_ker_iff (mR y) hg) h2d
  have hVu := mul_eq_one_comm.mp hVV
  have h1' : (1 : Matrix (Fin n) (Fin n) ℂ)ᴴ * 1 = 1 := by simp
  have hK := kmat_unit _ 1 hVu h1'
  have hK' := mul_eq_one_comm.mp hK
  let kGL : GL (Fin n ⊕ Fin n) ℂ := ⟨kmat ((u2 (mR y))⁻¹ * u1 (mR y)) 1, _, hK', hK⟩
  have hkG : kGL ∈ GR n := kmat_inG _ 1 hVu h1'
  let k : GR n := ⟨kGL, hkG⟩
  have hkK : k ∈ KR n := by
    show InK (kmat ((u2 (mR y))⁻¹ * u1 (mR y)) 1)
    exact ⟨kmat_inG _ 1 hVu h1', hK⟩
  refine ⟨y * k⁻¹, k, ?_, hkK, (inv_mul_cancel_right y k).symm⟩
  show toBlocks₂₁ (mR (y * k⁻¹)) = 0
  have hm : mR (y * k⁻¹) = mR y * (kmat ((u2 (mR y))⁻¹ * u1 (mR y)) 1)ᴴ := rfl
  rw [hm, proj_mul_mul_proj_of_ker_iff, Matrix.smul_mul, Matrix.smul_mul, haV, conjTranspose_one, Matrix.mul_one]
  simp

end PositivityTheory.Rg.Sw.AbsSt
