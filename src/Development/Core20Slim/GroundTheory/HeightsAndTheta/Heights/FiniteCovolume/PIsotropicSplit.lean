module

public import Mathlib
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.SecondCountableTopologyArchUnitary
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.MajorantInvolutionDiagonalForm
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PEigenspacesOrthogonal
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Pi
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Algebra.Star.Pi
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Tactic.LinearCombination.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open Matrix

theorem IsotropicSplit.proof (ι : Type*) [Fintype ι] [DecidableEq ι]
    (h₁ : EigenspacesOrthogonal.Statement ι) : IsotropicSplit.Statement ι := by
  intro H P hM z hz
  obtain ⟨hP, hH, hdet, hPHP⟩ := hM
  set A := majInvolution H P with hAdef
  have hA2 : A * A = 1 := by
    rw [hAdef, majInvolution, show H⁻¹ * P * (H⁻¹ * P) = H⁻¹ * (P * H⁻¹ * P) by
      simp only [Matrix.mul_assoc], hPHP, nonsing_inv_mul H hdet]
  have hPA : P * A = H := by
    rw [hAdef, majInvolution, ← Matrix.mul_assoc, hPHP]
  have hAA (v : ι → ℂ) : A *ᵥ (A *ᵥ v) = v := by
    rw [mulVec_mulVec, hA2, one_mulVec]
  set a := plusPart H P z with hadef
  set b := minusPart H P z with hbdef
  have ha : A *ᵥ a = a := by
    rw [hadef, plusPart, ← hAdef, mulVec_smul, mulVec_add, hAA, add_comm]
  have hb : A *ᵥ b = -b := by
    rw [hbdef, minusPart, ← hAdef, mulVec_smul, mulVec_sub, hAA, ← smul_neg, neg_sub]
  have hzab : z = a + b := by
    rw [hadef, hbdef, plusPart, minusPart, ← smul_add]
    ext i
    simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul]
    ring
  have hAzab : A *ᵥ z = a - b := by
    rw [hadef, hbdef, plusPart, minusPart, ← hAdef, ← smul_sub]
    ext i
    simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul]
    ring
  have hab : star a ⬝ᵥ (P *ᵥ b) = 0 := h₁ H P ⟨hP, hH, hdet, hPHP⟩ a b ha hb
  have hba : star b ⬝ᵥ (P *ᵥ a) = 0 := by
    rw [star_dotProduct, star_mulVec, ← dotProduct_mulVec, hP.1.eq, hab, star_zero]
  refine ⟨ha, hb, ?_⟩
  have h0 : star (a + b) ⬝ᵥ (P *ᵥ (a - b)) = 0 := by
    rw [← hAzab, ← hzab, mulVec_mulVec, hPA, hz]
  rw [star_add, add_dotProduct, mulVec_sub, dotProduct_sub, dotProduct_sub, hab, hba] at h0
  linear_combination h0

end GroundTheory.Heights₂.Heights.FiniteCovolume
