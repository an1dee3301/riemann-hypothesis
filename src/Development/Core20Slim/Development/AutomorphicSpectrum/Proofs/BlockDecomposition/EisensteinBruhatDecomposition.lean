module

public import Mathlib
public import Development.Core20Slim.Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.EisCellsDefs
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsBlockMatrixTwoByTwoFinEq
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SpanRangeComplementTransformStatement
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SameSpanTransferMatricesStatement
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianBlockSolutionExistsStatement
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Order.Lemmas
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Basic.ExistsUnique
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.RelClasses
public import Mathlib.RingTheory.Bialgebra.Basic
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result

@[expose] public section

noncomputable section
open scoped Matrix
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions.EC

namespace GlobalTheory.CompanionTheory.BruhatCell

variable {K : Type} [Field K]

theorem inv_block_of_unitary (σ : K →+* K) {n : ℕ} {A B C D : Matrix (Fin n) (Fin n) K}
    (h : IsUnitary σ (Jm K n) (blk4 A B C D)) :
    (blk4 A B C D)⁻¹ = blk4 (cT σ D) (-cT σ B) (-cT σ C) (cT σ A) := by
  rw [inv_of_unitary σ h, cT_blk4]
  unfold Jm
  rw [submatrix_fromBlocks_mul, submatrix_fromBlocks_mul, neg_block_matrix]
  congr 1 <;> simp

theorem isotropic_of_unitary (σ : K →+* K) {n : ℕ} {A B C D : Matrix (Fin n) (Fin n) K}
    (h : IsUnitary σ (Jm K n) (blk4 A B C D)) : C * cT σ D = D * cT σ C := by
  have h1 : blk4 A B C D * (blk4 A B C D)⁻¹ = 1 := Matrix.mul_nonsing_inv _ (isUnit_det_of_unitary σ h)
  rw [inv_block_of_unitary σ h, submatrix_fromBlocks_mul, ← block_matrix_one] at h1
  have := (blockMatrixTwoByTwoFin_injective h1).2.2.1
  rw [Matrix.mul_neg, ← sub_eq_add_neg, sub_eq_zero] at this
  exact this

theorem repMat_unitary (σ : K →+* K) (hσ : ∀ x, σ (σ x) = x) {n r : ℕ} (b : Matrix (Fin r) (Fin r) K)
    (a : Matrix (Fin n) (Fin n) K) (hb : cT σ b = b) (ha : IsUnit a.det) :
    IsUnit (repMat σ b a).det ∧ IsUnitary σ (Jm K n) (repMat σ b a) := by
  have hu : IsUnitary σ (Jm K n) (repMat σ b a) := by
    unfold repMat
    refine unitary_mul σ (unitary_mul σ ?_ ?_) ?_
    · unfold IsUnitary wr Jm
      rw [cT_blk4, submatrix_fromBlocks_mul, submatrix_fromBlocks_mul]
      have e2 := eId_mul_eId (K := K) n r
      simp only [cT_sub, cT_one, cT_neg, cT_eId]
      congr 1
      · simp only [mul_zero, zero_add, add_zero, Matrix.mul_one, Matrix.mul_neg, neg_neg, Matrix.sub_mul,
          Matrix.mul_sub, Matrix.one_mul, Matrix.neg_mul, e2]; abel
      · simp only [mul_zero, zero_add, add_zero, Matrix.mul_one, Matrix.mul_neg, neg_neg, Matrix.sub_mul,
          Matrix.mul_sub, Matrix.one_mul, Matrix.neg_mul, e2]; abel
      · simp only [mul_zero, zero_add, add_zero, Matrix.mul_one, Matrix.mul_neg, neg_neg, Matrix.sub_mul,
          Matrix.mul_sub, Matrix.one_mul, Matrix.neg_mul, e2]; abel
      · simp only [mul_zero, zero_add, add_zero, Matrix.mul_one, Matrix.mul_neg, neg_neg, Matrix.sub_mul,
          Matrix.mul_sub, Matrix.one_mul, Matrix.neg_mul, e2]; abel
    · unfold IsUnitary nB Jm
      have hB : cT σ (extB (n := n) b) = extB b := by rw [cT_extB, hb]
      rw [cT_blk4, submatrix_fromBlocks_mul, submatrix_fromBlocks_mul]
      simp [cT_one, cT_zero, hB]
    · unfold IsUnitary mA Jm
      have ha' := isUnit_det_cT σ ha
      rw [cT_blk4, submatrix_fromBlocks_mul, submatrix_fromBlocks_mul, cT_inv σ ha', cT_cT σ hσ]
      simp [cT_zero, Matrix.mul_nonsing_inv _ ha', Matrix.nonsing_inv_mul _ ha]
  exact ⟨isUnit_det_of_unitary σ hu, hu⟩

theorem siegel_rep_iff (σ : K →+* K) (hσ : ∀ x, σ (σ x) = x) {n r : ℕ} (b : Matrix (Fin r) (Fin r) K)
    (a : Matrix (Fin n) (Fin n) K) (hb : cT σ b = b) (ha : IsUnit a.det) (A B C D : Matrix (Fin n) (Fin n) K) :
    IsSiegelP (blk4 A B C D * (repMat σ b a)⁻¹) ↔
      C * a⁻¹ * (1 - eId K n r - extB b) + D * cT σ a * eId K n r = 0 := by
  have hu := (repMat_unitary σ hσ b a hb ha).2
  rw [repMat_eq] at hu ⊢
  rw [inv_block_of_unitary σ hu, submatrix_fromBlocks_mul, is_siegel_parabolic_block_iff]
  simp only [cT_mul, cT_neg, cT_sub, cT_one, cT_eId, cT_extB, hb, cT_inv σ (isUnit_det_cT σ ha), cT_cT σ hσ,
    neg_neg, Matrix.mul_neg, Matrix.mul_assoc]

theorem factor_of_siegel {n : ℕ} {g h : Matrix (Fin (n + n)) (Fin (n + n)) K} (hg : IsUnit g.det)
    (hh : IsUnit h.det) (hp : IsSiegelP (g * h⁻¹)) {A B C D A' B' C' D' : Matrix (Fin n) (Fin n) K}
    (eg : g = blk4 A B C D) (eh : h = blk4 A' B' C' D') :
    ∃ p : Matrix (Fin n) (Fin n) K, IsUnit p.det ∧ C = p * C' ∧ D = p * D' := by
  obtain ⟨p1, p2, p3, p4, hp'⟩ := exists_blockMatrixTwoByTwoFin_eq (g * h⁻¹)
  rw [hp', is_siegel_parabolic_block_iff] at hp
  subst hp
  have hgp : g = blk4 p1 p2 0 p4 * h := by
    rw [← hp', Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hh, Matrix.mul_one]
  have hdet : IsUnit (blk4 p1 p2 0 p4).det := by
    rw [← hp', Matrix.det_mul]; exact hg.mul (Matrix.isUnit_nonsing_inv_det _ hh)
  rw [det_block_lower_zero] at hdet
  rw [eg, eh, submatrix_fromBlocks_mul] at hgp
  have := blockMatrixTwoByTwoFin_injective hgp
  refine ⟨p4, isUnit_of_mul_isUnit_right hdet, ?_, ?_⟩
  · simpa using this.2.2.1
  · simpa using this.2.2.2

theorem herm_unique (σ : K →+* K) {n r : ℕ} (hr : r ≤ n) (a : Matrix (Fin n) (Fin n) K) (ha : IsUnit a.det)
    (b b' : Matrix (Fin r) (Fin r) K) (p p' : Matrix (Fin n) (Fin n) K) (hp : IsUnit p.det)
    (hC : p * -(eId K n r * a) = p' * -(eId K n r * a))
    (hD : p * ((1 - eId K n r - extB b) * (cT σ a)⁻¹) = p' * ((1 - eId K n r - extB b') * (cT σ a)⁻¹)) :
    b = b' := by
  have ha' := isUnit_det_cT σ ha
  have h1 : p * eId K n r = p' * eId K n r := by
    have := congrArg (· * a⁻¹) hC
    simpa [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ ha] using this
  have h2 : p * (1 - eId K n r - extB b) = p' * (1 - eId K n r - extB b') := by
    have := congrArg (· * cT σ a) hD
    simpa [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ ha'] using this
  have key : ∀ b₀ : Matrix (Fin r) (Fin r) K,
      (1 - eId K n r - extB b₀) * (1 - eId K n r) = 1 - eId K n r := by
    intro b₀
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, eId_mul_eId, extB_mul_eId]
    abel
  have h3 : p * (1 - eId K n r) = p' * (1 - eId K n r) := by
    calc p * (1 - eId K n r) = p * ((1 - eId K n r - extB b) * (1 - eId K n r)) := by rw [key]
      _ = p * (1 - eId K n r - extB b) * (1 - eId K n r) := by rw [Matrix.mul_assoc]
      _ = p' * (1 - eId K n r - extB b') * (1 - eId K n r) := by rw [h2]
      _ = p' * (1 - eId K n r) := by rw [Matrix.mul_assoc, key]
  have hpp : p = p' := by
    have e1 : ∀ q : Matrix (Fin n) (Fin n) K, q = q * eId K n r + q * (1 - eId K n r) := by
      intro q; rw [← Matrix.mul_add]; simp
    rw [e1 p, e1 p', h1, h3]
  subst hpp
  have := congrArg (p⁻¹ * ·) h2
  simp only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hp, Matrix.one_mul, sub_right_inj] at this
  exact extB_injective hr this

theorem bruhat : Bruhat := by
  intro K _ σ hσ _ n c hc a ha
  have hr : ∀ U : Submodule K (Fin n → K), Module.finrank K U ≤ n := fun U =>
    (Submodule.finrank_le U).trans (by simp)
  refine ⟨fun U b hb => repMat_unitary σ hσ b (a U) hb (ha U).1, ?_⟩
  intro g hg hgu
  obtain ⟨A, B, C, D, rfl⟩ := exists_blockMatrixTwoByTwoFin_eq g
  have hiso := isotropic_of_unitary σ hgu
  set U := Submodule.span K (Set.range C) with hU
  obtain ⟨T, L, hT, -, hLT⟩ := GlobalTheory.T.same_span_transfer_matrices C (c U) (hc U).1 (hc U).2
  obtain ⟨b, hb, hcond⟩ := GlobalTheory.T.hermitian_block_solution_exists σ hσ (hr U) (c U) (a U) C D T L (ha U) hT hLT hiso
  have hS := (siegel_rep_iff σ hσ b (a U) hb (ha U).1 A B C D).2 hcond
  refine ⟨⟨U, b, hb⟩, hS, ?_⟩
  rintro ⟨U', b', hb'⟩ hq
  have hrep' := repMat_unitary σ hσ b' (a U') hb' (ha U').1
  obtain ⟨p', hp', hC', hD'⟩ := factor_of_siegel hg hrep'.1 hq rfl (repMat_eq σ b' (a U'))
  have hUU : U' = U := by
    rw [← (hc U').2, ← GlobalTheory.T.span_range_complement_transform (hr U') (c U') (a U') p' (ha U') hp', ← hC']
  subst hUU
  have hrep := repMat_unitary σ hσ b (a U) hb (ha U).1
  obtain ⟨p, hp, hC, hD⟩ := factor_of_siegel hg hrep.1 hS rfl (repMat_eq σ b (a U))
  have hbb := herm_unique σ (hr U) (a U) (ha U).1 b' b p' p hp' (hC'.symm.trans hC) (hD'.symm.trans hD)
  subst hbb
  rfl

end GlobalTheory.CompanionTheory.BruhatCell
