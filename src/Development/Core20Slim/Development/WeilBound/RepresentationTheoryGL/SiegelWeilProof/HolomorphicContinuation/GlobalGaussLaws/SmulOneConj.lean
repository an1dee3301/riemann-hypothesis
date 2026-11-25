module

public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DifferenceQuotientIsometryExchangeAlt
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobData
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GaussLaw
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.IsSingTest
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Algebra.Star.Pi
public import Mathlib.Analysis.CStarAlgebra.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Int.Cast.Lemmas
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Block
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

noncomputable section

open Matrix
open scoped ComplexOrder

namespace PositivityTheory.Rg.Sw.Glob

namespace DRealH

variable {n : ℕ}

theorem blocks_of_inG {g : M2 n} (hg : InG g) :
    (g.toBlocks₁₁)ᴴ * g.toBlocks₂₁ = (g.toBlocks₂₁)ᴴ * g.toBlocks₁₁ ∧
    (g.toBlocks₁₂)ᴴ * g.toBlocks₂₂ = (g.toBlocks₂₂)ᴴ * g.toBlocks₁₂ ∧
    (g.toBlocks₁₁)ᴴ * g.toBlocks₂₂ - (g.toBlocks₂₁)ᴴ * g.toBlocks₁₂ = 1 ∧
    (g.toBlocks₁₂)ᴴ * g.toBlocks₂₁ - (g.toBlocks₂₂)ᴴ * g.toBlocks₁₁ = -1 := by
  have h := hg
  unfold InG JJ at h
  rw [← Matrix.fromBlocks_toBlocks g, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_multiply] at h
  simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.mul_neg, Matrix.neg_mul, zero_add, add_zero,
    Matrix.fromBlocks_inj] at h
  obtain ⟨h11, h12, h21, h22⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := congrArg (· + (g.toBlocks₂₁)ᴴ * g.toBlocks₁₁) h11
    simpa [Matrix.mul_assoc, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
  · have := congrArg (· + (g.toBlocks₂₂)ᴴ * g.toBlocks₁₂) h22
    simpa [Matrix.mul_assoc, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
  · simpa [Matrix.mul_assoc, sub_eq_add_neg, add_comm] using h12
  · simpa [Matrix.mul_assoc, sub_eq_add_neg, add_comm] using h21

variable {A B C D : Matrix (Fin n) (Fin n) ℂ}

theorem smul_one_conj (w : ℂ) : ((w • (1 : Matrix (Fin n) (Fin n) ℂ)))ᴴ = (star w) • 1 := by
  rw [conjTranspose_smul, conjTranspose_one]

theorem cross_self (h1 : Aᴴ * C = Cᴴ * A) (h2 : Bᴴ * D = Dᴴ * B) (h3 : Aᴴ * D - Cᴴ * B = 1) (h4 : Bᴴ * C - Dᴴ * A = -1)
    (w : ℂ) : (w • A + B)ᴴ * (w • C + D) - (w • C + D)ᴴ * (w • A + B) = (star w - w) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  have e3 : Aᴴ * D = 1 + Cᴴ * B := by rw [← h3]; abel
  have e4 : Bᴴ * C = -1 + Dᴴ * A := by rw [← h4]; abel
  simp only [conjTranspose_add, conjTranspose_smul, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, e3, e4, h1, h2]
  module

theorem cross_conj (h1 : Aᴴ * C = Cᴴ * A) (h2 : Bᴴ * D = Dᴴ * B) (h3 : Aᴴ * D - Cᴴ * B = 1) (h4 : Bᴴ * C - Dᴴ * A = -1)
    (w : ℂ) : (w • A + B)ᴴ * ((star w) • C + D) = (w • C + D)ᴴ * ((star w) • A + B) := by
  have e3 : Aᴴ * D = 1 + Cᴴ * B := eq_add_of_sub_eq h3
  have e4 : Bᴴ * C = -1 + Dᴴ * A := eq_add_of_sub_eq h4
  simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.add_mul, Matrix.mul_add,
    Matrix.smul_mul, Matrix.mul_smul]
  rw [h1, h2, e3, e4]
  module

theorem det_ne_zero (h1 : Aᴴ * C = Cᴴ * A) (h2 : Bᴴ * D = Dᴴ * B) (h3 : Aᴴ * D - Cᴴ * B = 1) (h4 : Bᴴ * C - Dᴴ * A = -1)
    (w : ℂ) (hw : star w ≠ w) : (w • C + D).det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have key := cross_self h1 h2 h3 h4 w
  have e := congrArg (fun M => star v ⬝ᵥ (M *ᵥ v)) key
  have l1 : ((w • A + B)ᴴ * (w • C + D) - (w • C + D)ᴴ * (w • A + B)) *ᵥ v
      = -((w • C + D)ᴴ *ᵥ ((w • A + B) *ᵥ v)) := by
    rw [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero, zero_sub]
  have l2 : ((star w - w) • (1 : Matrix (Fin n) (Fin n) ℂ)) *ᵥ v = (star w - w) • v := by
    ext i
    simp [Matrix.mulVec, dotProduct, Matrix.one_apply]
  simp only [l1, l2] at e
  rw [dotProduct_neg, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec, hv, star_zero, zero_dotProduct, neg_zero,
    dotProduct_smul, smul_eq_mul] at e
  have hne : star w - w ≠ 0 := sub_ne_zero.mpr hw
  have : star v ⬝ᵥ v = 0 := (mul_eq_zero.mp e.symm).resolve_left hne
  exact hv0 (dotProduct_star_self_eq_zero.mp this)

theorem conj_frac (h1 : Aᴴ * C = Cᴴ * A) (h2 : Bᴴ * D = Dᴴ * B) (h3 : Aᴴ * D - Cᴴ * B = 1) (h4 : Bᴴ * C - Dᴴ * A = -1)
    (w : ℂ) (hw : star w ≠ w) :
    ((w • A + B) * (w • C + D)⁻¹)ᴴ = ((star w) • A + B) * ((star w) • C + D)⁻¹ := by
  have hw' : star (star w) ≠ star w := by
    rw [star_star]
    exact fun h => hw h.symm
  have d1 := det_ne_zero h1 h2 h3 h4 w hw
  have d2 := det_ne_zero h1 h2 h3 h4 (star w) hw'
  have u1 : IsUnit (w • C + D)ᴴ.det := by
    rw [Matrix.det_conjTranspose]
    exact (star_ne_zero.mpr d1).isUnit
  have u2 : IsUnit ((star w) • C + D).det := d2.isUnit
  have cc := cross_conj h1 h2 h3 h4 w
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_nonsing_inv]
  calc ((w • C + D)ᴴ)⁻¹ * (w • A + B)ᴴ
      = ((w • C + D)ᴴ)⁻¹ * ((w • A + B)ᴴ * ((star w) • C + D)) * ((star w) • C + D)⁻¹ := by
        rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_right _ _ u2]
    _ = ((w • C + D)ᴴ)⁻¹ * ((w • C + D)ᴴ * ((star w) • A + B)) * ((star w) • C + D)⁻¹ := by rw [cc]
    _ = ((star w) • A + B) * ((star w) • C + D)⁻¹ := by
        rw [Matrix.nonsing_inv_mul_cancel_left _ _ u1]

end DRealH

open DRealH in
theorem dReal : DReal := by
  intro m n ε t c e y X a ha s
  funext u
  have hA : aC X (s : ℂ) = mR (a s) := by
    rw [ha s]
    unfold aC
    congr 1
    · congr 1
      funext j
      rw [Complex.ofReal_exp, Complex.ofReal_mul]
    · congr 1
      funext j
      rw [Complex.ofReal_exp, Complex.ofReal_neg, Complex.ofReal_mul]
  have hmul : mR y * aC X (s : ℂ) = mR (y * a s) := by
    rw [hA]
    rfl
  have hG : InG (mR (y * a s)) := (y * a s).2
  obtain ⟨h1, h2, h3, h4⟩ := blocks_of_inG hG
  have hIs : star Complex.I ≠ Complex.I := by
    rw [Complex.star_def, Complex.conj_I]
    intro h
    have := congrArg Complex.im h
    simp at this
    norm_num at this
  have key := conj_frac h1 h2 h3 h4 Complex.I hIs
  have sI : star Complex.I = -Complex.I := by rw [Complex.star_def, Complex.conj_I]
  rw [sI] at key
  have cI : ((Complex.I • (1 : Matrix (Fin n) (Fin n) ℂ)))ᴴ = (-Complex.I) • 1 := by
    rw [smul_one_conj, sI]
  unfold famC jF gZf gC jC ptZ actZ
  simp only [hmul, cI, Matrix.mul_smul, Matrix.mul_one]
  rw [key]

end PositivityTheory.Rg.Sw.Glob
