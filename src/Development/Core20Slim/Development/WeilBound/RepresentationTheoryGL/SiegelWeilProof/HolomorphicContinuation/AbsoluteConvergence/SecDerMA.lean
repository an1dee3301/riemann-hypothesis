module

public import Mathlib
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.SecDerMSt
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.WeightFactorDilation
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDensityOfImmersion
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.DerivativeVacuumDilationsAlt
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobData
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LamSing
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.ReidxConjTranspose
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.IsSingTest
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Block
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

open Matrix

namespace PositivityTheory.Rg.Sw.AbsSt.SDM

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt

variable {n : ℕ}

theorem aE_neg (H : Matrix (Fin n) (Fin n) ℂ) (σ : ℝ) : aE H (-σ) = NormedSpace.exp (-((σ : ℂ) • H)) := by
  simp [aE, neg_smul]

theorem aE_mul_neg (H : Matrix (Fin n) (Fin n) ℂ) (σ : ℝ) : aE H (-σ) * aE H σ = 1 := by
  rw [aE_neg, aE, Matrix.exp_neg]
  exact Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 (Matrix.isUnit_exp _))

theorem aE_mul_neg' (H : Matrix (Fin n) (Fin n) ℂ) (σ : ℝ) : aE H σ * aE H (-σ) = 1 := by
  rw [aE_neg, aE, Matrix.exp_neg]
  exact Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (Matrix.isUnit_exp _))

theorem aE_herm {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.IsHermitian) (σ : ℝ) : (aE H σ)ᴴ = aE H σ := by
  rw [aE, ← Matrix.exp_conjTranspose, Matrix.conjTranspose_smul, hH.eq]
  congr 1
  simp

theorem det_aE (H : Matrix (Fin n) (Fin n) ℂ) (σ : ℝ) : (aE H σ).det = Complex.exp ((σ : ℂ) * H.trace) := by
  rw [aE, GlobalTheory.SUVol.det_exp, Matrix.trace_smul, smul_eq_mul]

private theorem JJ_mul_self_eq_neg_one (n : ℕ) : JJ n * JJ n = -1 := by
  rw [JJ, fromBlocks_multiply, ← fromBlocks_one, fromBlocks_neg]
  simp
private theorem mul_JJ_mul_conjTranspose_eq_JJ_of_inG {n : ℕ} (G Gi : M2 n) (hGi : G * Gi = 1) (hG : InG G) :
    G * JJ n * Gᴴ = JJ n := by
  have hJ := JJ_mul_self_eq_neg_one n
  have h1 : Gᴴ * JJ n = JJ n * Gi := by
    calc Gᴴ * JJ n = Gᴴ * JJ n * (G * Gi) := by rw [hGi, Matrix.mul_one]
      _ = (Gᴴ * JJ n * G) * Gi := by simp only [Matrix.mul_assoc]
      _ = JJ n * Gi := by rw [hG]
  calc G * JJ n * Gᴴ = G * JJ n * Gᴴ * (JJ n * (-JJ n)) := by
        rw [Matrix.mul_neg, hJ, neg_neg, Matrix.mul_one]
    _ = G * (JJ n * (Gᴴ * JJ n)) * (-JJ n) := by simp only [Matrix.mul_assoc]
    _ = G * ((JJ n * JJ n) * Gi) * (-JJ n) := by rw [h1]; simp only [Matrix.mul_assoc]
    _ = JJ n := by
        rw [hJ]
        simp [hGi]
private theorem exists_GR_mR_eq_of_inG_of_inverse {n : ℕ} (M Mi : M2 n) (h1 : M * Mi = 1) (h2 : Mi * M = 1)
    (hM : InG M) : ∃ x : GR n, mR x = M ∧ mR x⁻¹ = Mi :=
  ⟨⟨⟨M, Mi, h1, h2⟩, hM⟩, rfl, rfl⟩
private theorem inG_JJ_mul_nU_of_isHermitian {n : ℕ} (c : Matrix (Fin n) (Fin n) ℂ) (hc : c.IsHermitian) :
    InG (JJ n * nU c) := by
  unfold InG JJ nU
  rw [fromBlocks_multiply, fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply]
  simp [hc.eq]
private theorem inG_fromBlocks_diag_of_hermitian_inverse {n : ℕ} (a a' : Matrix (Fin n) (Fin n) ℂ) (ha : a.IsHermitian)
    (ha' : a'.IsHermitian) (h : a * a' = 1) (h' : a' * a = 1) :
    InG (fromBlocks a' 0 0 a) := by
  unfold InG JJ
  rw [fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply, ha.eq, ha'.eq]
  simp [h, h']

theorem cellM : CellM := by
  intro n H hH f hf g hC
  have hG : mR g = fromBlocks (toBlocks₁₁ (mR g)) (toBlocks₁₂ (mR g)) (toBlocks₂₁ (mR g))
      (toBlocks₂₂ (mR g)) := (fromBlocks_toBlocks _).symm
  set A := toBlocks₁₁ (mR g)
  set B := toBlocks₁₂ (mR g)
  set C := toBlocks₂₁ (mR g)
  set D := toBlocks₂₂ (mR g)
  have hCu : IsUnit C.det := isUnit_iff_ne_zero.mpr hC
  have hgi : mR g * mR g⁻¹ = 1 := congrArg mR (mul_inv_cancel g)
  have hgJ : mR g * JJ n * (mR g)ᴴ = JJ n := mul_JJ_mul_conjTranspose_eq_JJ_of_inG (mR g) (mR g⁻¹) hgi g.2
  have hCD : C * Dᴴ = D * Cᴴ := by
    have h22 := congrArg toBlocks₂₂ hgJ
    rw [hG, JJ, fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply] at h22
    simp at h22
    exact ((neg_add_eq_zero).mp h22).symm
  have hCHu : IsUnit Cᴴ.det := by
    rw [det_conjTranspose]
    exact hCu.star
  have hbH : (C⁻¹ * D).IsHermitian := by
    unfold IsHermitian
    rw [conjTranspose_mul, conjTranspose_nonsing_inv]
    calc Dᴴ * (Cᴴ)⁻¹ = C⁻¹ * (C * Dᴴ) * (Cᴴ)⁻¹ := by
          rw [← Matrix.mul_assoc, nonsing_inv_mul _ hCu, Matrix.one_mul]
      _ = C⁻¹ * (D * Cᴴ) * (Cᴴ)⁻¹ := by rw [hCD]
      _ = C⁻¹ * D := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, mul_nonsing_inv _ hCHu, Matrix.mul_one]
  have hnU : ∀ c : Matrix (Fin n) (Fin n) ℂ, nU c * nU (-c) = 1 ∧ nU (-c) * nU c = 1 := by
    intro c
    constructor <;> rw [nU, nU, fromBlocks_multiply, ← fromBlocks_one] <;> simp
  have hJ := JJ_mul_self_eq_neg_one n
  have hWinv : ∀ c : Matrix (Fin n) (Fin n) ℂ,
      JJ n * nU c * (nU (-c) * -JJ n) = 1 ∧ nU (-c) * -JJ n * (JJ n * nU c) = 1 := by
    intro c
    constructor
    · rw [Matrix.mul_assoc, ← Matrix.mul_assoc (nU c), (hnU c).1, Matrix.one_mul, Matrix.mul_neg, hJ,
        neg_neg]
    · rw [Matrix.mul_assoc, ← Matrix.mul_assoc (-JJ n), Matrix.neg_mul, hJ, neg_neg, Matrix.one_mul,
        (hnU c).2]
  obtain ⟨w₀, hw₀, hw₀i⟩ := exists_GR_mR_eq_of_inG_of_inverse _ _ (hWinv (C⁻¹ * D)).1 (hWinv (C⁻¹ * D)).2
    (inG_JJ_mul_nU_of_isHermitian _ hbH)
  refine ⟨g * w₀⁻¹, C⁻¹ * D, ?_, hbH, ?_⟩
  · show toBlocks₂₁ (mR g * mR w₀⁻¹) = 0
    rw [hw₀i, hG, nU, JJ, fromBlocks_neg, fromBlocks_multiply, fromBlocks_multiply]
    simp [← Matrix.mul_assoc, mul_nonsing_inv _ hCu]
  intro p q e σ
  have h1 : aE H σ * aE H (-σ) = 1 := aE_mul_neg' H σ
  have h2 : aE H (-σ) * aE H σ = 1 := aE_mul_neg H σ
  have ha : (aE H σ).IsHermitian := aE_herm hH σ
  have ha' : (aE H (-σ)).IsHermitian := aE_herm hH (-σ)
  have hc : (aE H (-σ) * (C⁻¹ * D) * aE H (-σ)).IsHermitian := by
    unfold IsHermitian
    rw [conjTranspose_mul, conjTranspose_mul, ha'.eq, hbH.eq, ← Matrix.mul_assoc]
  obtain ⟨mA, hmA, -⟩ := exists_GR_mR_eq_of_inG_of_inverse (fromBlocks (aE H (-σ)) 0 0 (aE H σ))
    (fromBlocks (aE H σ) 0 0 (aE H (-σ)))
    (by rw [fromBlocks_multiply, ← fromBlocks_one]; simp [h1, h2])
    (by rw [fromBlocks_multiply, ← fromBlocks_one]; simp [h1, h2])
    (inG_fromBlocks_diag_of_hermitian_inverse _ _ ha ha' h1 h2)
  obtain ⟨w, hw, -⟩ := exists_GR_mR_eq_of_inG_of_inverse _ _ (hWinv (aE H (-σ) * (C⁻¹ * D) * aE H (-σ))).1
    (hWinv _).2 (inG_JJ_mul_nU_of_isHermitian _ hc)
  refine ⟨mA, w, ?_, ?_, hw, hc, ?_⟩
  · show toBlocks₂₁ (mR mA) = 0
    rw [hmA]
    simp
  · unfold F0 f0 u1 u2
    rw [hmA]
    simp only [toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂, smul_zero, zero_add, neg_zero,
      det_fromBlocks_zero₂₁]
    rw [← det_mul, h2, det_one, _root_.one_zpow, one_mul, det_aE, ← Complex.exp_int_mul,
      ← Complex.exp_int_mul, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  · apply Subtype.ext
    apply Units.ext
    show mR g * mR (f σ) = mR g * mR w₀⁻¹ * mR mA * mR w
    rw [hf σ, hw₀i, hmA, hw, Matrix.mul_assoc (mR g), Matrix.mul_assoc (mR g)]
    congr 1
    change fromBlocks (aE H σ) 0 0 (NormedSpace.exp (-((σ : ℂ) • H))) = _
    rw [← aE_neg, nU, nU, JJ, fromBlocks_neg]
    simp [fromBlocks_multiply, ← Matrix.mul_assoc, h1]

end PositivityTheory.Rg.Sw.AbsSt.SDM
