module

public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GaussJ
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobData
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GaussSt
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.ReidxConjTranspose
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.IsSingTest
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Invertible.Basic
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Algebra.Star.Pi
public import Mathlib.Algebra.Star.SelfAdjoint
public import Mathlib.Analysis.CStarAlgebra.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.NonUnital
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.Real.Star
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Block
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.InvariantBasisNumber
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Algebra.Star.Real
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.Defs
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

open scoped Matrix ComplexOrder
open Matrix

namespace PositivityTheory.Rg.Sw.Glob

open GaussH

private theorem fromBlocks_unitary_and_conj_JJ_eq {n : ℕ} (X Y : Matrix (Fin n) (Fin n) ℂ) (h1 : Xᴴ * X + Yᴴ * Y = 1)
    (h2 : Xᴴ * Y = Yᴴ * X) :
    (fromBlocks X (-Y) Y X)ᴴ * fromBlocks X (-Y) Y X = 1 ∧
      (fromBlocks X (-Y) Y X)ᴴ * JJ n * fromBlocks X (-Y) Y X = JJ n := by
  constructor
  · rw [fromBlocks_conjTranspose, fromBlocks_multiply, ← fromBlocks_one]
    simp [h2]
    rw [h1, add_comm, h1, fromBlocks_one]
  · rw [JJ, fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply]
    simp [h2]
    exact ⟨by rw [add_comm, h1], by rw [← neg_add, h1]⟩

private theorem exists_normalizing_factor_of_left_inverse {n : ℕ} (X Y A B : Matrix (Fin n) (Fin n) ℂ) (h : A * X + B * Y = 1) :
    ∃ R : Matrix (Fin n) (Fin n) ℂ, (X * R)ᴴ * (X * R) + (Y * R)ᴴ * (Y * R) = 1 := by
  classical
  set M := Xᴴ * X + Yᴴ * Y with hM
  have hpsd : M.PosSemidef :=
    (posSemidef_conjTranspose_mul_self X).add (posSemidef_conjTranspose_mul_self Y)
  have hdet : M.det ≠ 0 := by
    intro h0
    obtain ⟨v, hv, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    have hq : star v ⬝ᵥ M *ᵥ v = 0 := by rw [hMv, dotProduct_zero]
    simp_rw [hM, add_mulVec, dotProduct_add, ← mulVec_mulVec, dotProduct_mulVec _ _ (X *ᵥ v),
      dotProduct_mulVec _ _ (Y *ᵥ v), vecMul_conjTranspose, star_star] at hq
    have h2 := (add_eq_zero_iff_of_nonneg (dotProduct_star_self_nonneg _)
      (dotProduct_star_self_nonneg _)).mp hq
    have hx := dotProduct_star_self_eq_zero.mp h2.1
    have hy := dotProduct_star_self_eq_zero.mp h2.2
    apply hv
    rw [← one_mulVec v, ← h, add_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, hx, hy, mulVec_zero,
      mulVec_zero, add_zero]
  open scoped MatrixOrder in
  obtain ⟨S, hSS, hSa⟩ : ∃ S : Matrix (Fin n) (Fin n) ℂ, S * S = M ∧ Sᴴ = S :=
    ⟨CFC.sqrt M, CFC.sqrt_mul_sqrt_self M hpsd.nonneg, (CFC.sqrt_nonneg M).isSelfAdjoint⟩
  have hS : IsUnit S.det := by
    rw [isUnit_iff_ne_zero]
    intro h0
    apply hdet
    rw [← hSS, det_mul, h0, zero_mul]
  refine ⟨S⁻¹, ?_⟩
  simp only [conjTranspose_mul, conjTranspose_nonsing_inv, hSa]
  calc S⁻¹ * Xᴴ * (X * S⁻¹) + S⁻¹ * Yᴴ * (Y * S⁻¹) = S⁻¹ * (S * S) * S⁻¹ := by
        rw [hSS, hM]; noncomm_ring
    _ = 1 := by rw [← mul_assoc, nonsing_inv_mul _ hS, one_mul, mul_nonsing_inv _ hS]

private theorem exists_mul_lower_zero_and_inK_of_normalized (n : ℕ) (y : GR n) (X Y C D R : Matrix (Fin n) (Fin n) ℂ)
    (hb : C * X + D * Y = 0) (hR : (X * R)ᴴ * (X * R) + (Y * R)ᴴ * (Y * R) = 1)
    (hiso' : (X * R)ᴴ * (Y * R) = (Y * R)ᴴ * (X * R)) (hC : toBlocks₂₁ (mR y) = C)
    (hD : toBlocks₂₂ (mR y) = D) :
    ∃ (p : ↥(GR n)) (k : ↥(GR n)), y = p * k ∧ toBlocks₂₁ (mR p) = 0 ∧ InK (mR k) := by
  obtain ⟨hU, hS⟩ := fromBlocks_unitary_and_conj_JJ_eq (X * R) (Y * R) hR hiso'
  generalize hkv : fromBlocks (X * R) (-(Y * R)) (Y * R) (X * R) = kv at hU hS
  have hU' : kv * kvᴴ = 1 := mul_eq_one_comm.mp hU
  have hu : (⟨kv, kvᴴ, hU', hU⟩ : GL (Fin n ⊕ Fin n) ℂ) ∈ GR n := hS
  refine ⟨y * ⟨_, hu⟩, (⟨_, hu⟩ : GR n)⁻¹, (mul_inv_cancel_right y _).symm, ?_, ?_⟩
  · have hm : mR (y * ⟨_, hu⟩) = mR y * kv := rfl
    rw [hm, ← hkv, ← fromBlocks_toBlocks (mR y), fromBlocks_multiply, toBlocks_fromBlocks₂₁, hC, hD,
      ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.add_mul, hb, Matrix.zero_mul]
  · refine ⟨(⟨_, hu⟩ : GR n)⁻¹.2, ?_⟩
    have hm : mR (⟨_, hu⟩ : GR n)⁻¹ = kvᴴ := rfl
    rw [hm, conjTranspose_conjTranspose]
    exact hU'

theorem iwaGR : IwaGR := by
  intro n y
  classical
  have hprod : mR y * mR y⁻¹ = 1 := by simp [mR]
  have hG : InG (mR y⁻¹) := (y⁻¹).2
  have hiso : (toBlocks₁₁ (mR y⁻¹))ᴴ * toBlocks₂₁ (mR y⁻¹) =
      (toBlocks₂₁ (mR y⁻¹))ᴴ * toBlocks₁₁ (mR y⁻¹) := by
    have h := congrArg toBlocks₁₁ hG
    rw [← fromBlocks_toBlocks (mR y⁻¹), JJ, fromBlocks_conjTranspose, fromBlocks_multiply,
      fromBlocks_multiply] at h
    simp at h
    exact (neg_add_eq_zero.mp h).symm
  have hb := hprod
  rw [← fromBlocks_toBlocks (mR y), ← fromBlocks_toBlocks (mR y⁻¹), fromBlocks_multiply,
    ← fromBlocks_one, fromBlocks_inj] at hb
  obtain ⟨R, hR⟩ := exists_normalizing_factor_of_left_inverse _ _ _ _ hb.1
  have hiso' : (toBlocks₁₁ (mR y⁻¹) * R)ᴴ * (toBlocks₂₁ (mR y⁻¹) * R) =
      (toBlocks₂₁ (mR y⁻¹) * R)ᴴ * (toBlocks₁₁ (mR y⁻¹) * R) := by
    simp only [conjTranspose_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc _ _ R, hiso, Matrix.mul_assoc]
  exact exists_mul_lower_zero_and_inK_of_normalized n y _ _ _ _ R hb.2.2.1 hR hiso' rfl rfl

end PositivityTheory.Rg.Sw.Glob
