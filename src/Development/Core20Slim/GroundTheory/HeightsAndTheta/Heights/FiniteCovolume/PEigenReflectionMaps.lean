module

public import Mathlib
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.SecondCountableTopologyArchUnitary
public import Batteries.Logic
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.MajorantInvolutionDiagonalForm
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
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
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Algebra.Star.Pi
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Tactic.FieldSimp.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open Matrix
open scoped ComplexOrder

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]


omit [DecidableEq ι] in
theorem star_dotProduct_mulVec_of_isHermitian {P : Matrix ι ι ℂ} (hP : P.IsHermitian)
    (x y : ι → ℂ) : star (star y ⬝ᵥ (P *ᵥ x)) = star x ⬝ᵥ (P *ᵥ y) := by
  have h1 : star y ⬝ᵥ (P *ᵥ x) = star (P *ᵥ y) ⬝ᵥ x := by
    rw [dotProduct_mulVec, star_mulVec, hP.eq]
  rw [h1, star_dotProduct, star_star]

theorem exists_unit_mul_star_eq_norm (s : ℂ) : ∃ α : ℂ, ‖α‖ = 1 ∧ α * star s = ‖s‖ ∧ star α * s = ‖s‖ := by
  by_cases hs : s = 0
  · exact ⟨1, by simp, by simp [hs], by simp [hs]⟩
  · have hn : (‖s‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hs
    refine ⟨s / ‖s‖, ?_, ?_, ?_⟩
    · rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_norm, div_self (norm_ne_zero_iff.mpr hs)]
    · rw [div_mul_eq_mul_div, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      field_simp
      push_cast; ring
    · rw [star_div₀, Complex.star_def, Complex.conj_ofReal, div_mul_eq_mul_div, mul_comm,
        Complex.mul_conj, Complex.normSq_eq_norm_sq]
      field_simp
      push_cast; ring


variable (ι) in
theorem EigenReflectionMaps.proof (h₁ : EigenReflection.Statement ι)
    (h₂ : EigenspacesOrthogonal.Statement ι) : EigenReflectionMaps.Statement ι := by
  intro H P hMaj ε hε a a' ha ha' hρ
  have hPh : P.IsHermitian := hMaj.1.isHermitian
  obtain ⟨α, hα1, hαs, hαs'⟩ := exists_unit_mul_star_eq_norm (star a ⬝ᵥ (P *ᵥ a'))
  refine ⟨α, hα1, ?_⟩
  set v : ι → ℂ := a' - α • a with hv
  by_cases hv0 : v = 0
  · refine ⟨1, by simp, by simp, ?_, fun u _ => by simp⟩
    rw [one_mulVec]
    exact sub_eq_zero.mp hv0
  have hAv : majInvolution H P *ᵥ v = ε • v := by
    rw [hv, mulVec_sub, mulVec_smul, ha, ha', smul_sub, smul_comm]
  obtain ⟨hRP, hRH, hRv, hRfix⟩ := h₁ H P hMaj ε hε v hv0 hAv
  refine ⟨pReflection P v, hRP, hRH, ?_, ?_⟩
  ·
    have hconj : star a' ⬝ᵥ (P *ᵥ a) = star (star a ⬝ᵥ (P *ᵥ a')) :=
      (star_dotProduct_mulVec_of_isHermitian hPh a' a).symm
    have hαα : star α * α = 1 := by
      rw [Complex.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hα1]; simp
    have hw : star v ⬝ᵥ (P *ᵥ (a' + α • a)) = 0 := by
      rw [hv, star_sub, star_smul, mulVec_add, mulVec_smul, sub_dotProduct, dotProduct_add,
        dotProduct_add, smul_dotProduct, smul_dotProduct, dotProduct_smul, dotProduct_smul,
        hconj, smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul, ← hρ]
      have e1 : star α * (α * (star a ⬝ᵥ (P *ᵥ a))) = (star α * α) * (star a ⬝ᵥ (P *ᵥ a)) := by
        ring
      rw [e1, hαα, hαs, hαs']
      ring
    have hRw := hRfix _ hw
    have hsplit : a' = (1 / 2 : ℂ) • (a' + α • a) + (1 / 2 : ℂ) • v := by
      rw [hv]; ext i; simp; ring
    rw [hsplit, mulVec_add, mulVec_smul, mulVec_smul, hRw, hRv, hv]
    ext i; simp; ring
  · intro u hu
    apply hRfix
    rcases hε with rfl | rfl
    · have h := h₂ H P hMaj v u (by rw [hAv, one_smul]) (by rw [hu, neg_smul, one_smul])
      exact h
    · have h := h₂ H P hMaj u v (by rw [hu, neg_neg, one_smul]) (by rw [hAv, neg_smul, one_smul])
      rw [← star_dotProduct_mulVec_of_isHermitian hPh, h, star_zero]

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
