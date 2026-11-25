module

public import Mathlib
public import Development.Core20Slim.Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.LocalDefs
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResAlgSplitTwo
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FixedNondeg
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedQuotientCardStatement
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianMatrixDiagonalizableStatement
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaussSumHermitianNormLevelShiftStatement
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaussSumHermitianNormLevelOneStatement
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CardRangeMulQuotientBoundedLevelStatement
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatrixGaussSumDiagonalFactorStatement
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatrixGaussSumCongrInvarianceStatement
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultiplicityReductionDiagonalProdStatement
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianCharacterOrthogonality
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianRepCountFourierExpansion
public import Init.Classical
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Int.Lemmas
public import Init.Data.Int.Order
public import Init.Data.Nat.Lemmas
public import Init.Data.Zero
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Divisibility.Units
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Quotient
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Nat.Log
public import Mathlib.Data.Set.CoeSort
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

noncomputable section
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.SiegLoc Filter Topology
namespace GlobalTheory.CompanionTheory.SiegLoc

theorem gauss1 {R : Type} [CommRing R] {σ : R →+* R} {ϖ : R} {q : ℕ} {ε : ℤ} (hR : IsUnrQuad R σ ϖ q ε)
    [∀ k, Fintype (R ⧸ lev ϖ k)] {ψ : ∀ k, AddChar (R ⧸ lev ϖ k) ℂ} (hψ : IsLevelChars σ ϖ ψ)
    (hε : (ε : ℂ) ^ 2 = 1) (j : ℕ) (a : R) (ha : σ a = a) (ha' : a ∉ lev ϖ 1) :
    (∑ w : R ⧸ lev ϖ j, ψ j (Ideal.Quotient.mk (lev ϖ j) a * (barσ σ ϖ hR.fix_ϖ j w * w))) = ((ε : ℂ) * q) ^ j := by
  induction j using Nat.twoStepInduction with
  | zero =>
    have : Subsingleton (R ⧸ lev ϖ 0) := Ideal.Quotient.subsingleton_iff.2 (by simp [lev])
    rw [Fintype.sum_subsingleton _ 0]
    simp
  | one => simpa using GlobalTheory.T.gauss_sum_hermitian_norm_level_one R σ ϖ q ε hR ψ hψ a ha ha'
  | more j ih _ =>
    rw [GlobalTheory.T.gauss_sum_hermitian_norm_level_shift R σ ϖ q ε hR ψ hψ j a ha ha', ih, pow_add, mul_pow (ε : ℂ) (q : ℂ) 2, hε]
    ring

theorem gauss_full {R : Type} [CommRing R] {σ : R →+* R} {ϖ : R} {q : ℕ} {ε : ℤ} (hR : IsUnrQuad R σ ϖ q ε)
    [∀ k, Fintype (R ⧸ lev ϖ k)] {ψ : ∀ k, AddChar (R ⧸ lev ϖ k) ℂ} (hψ : IsLevelChars σ ϖ ψ)
    (hε : (ε : ℂ) ^ 2 = 1) {m n : ℕ} (k : ℕ) (S : Matrix (Fin m) (Fin m) R) (hS : IsUnimod σ S)
    (B : Matrix (Fin n) (Fin n) (R ⧸ lev ϖ k)) (hB : B ∈ hermMod σ ϖ n k) :
    (∑ x : Matrix (Fin m) (Fin n) (R ⧸ lev ϖ k), ψ k (Matrix.trace (B * (cT (barσ σ ϖ hR.fix_ϖ k) x * red ϖ k S * x)))) =
      (Nat.card (Matrix (Fin m) (Fin n) (R ⧸ lev ϖ k)) : ℂ) * (((ε : ℂ) ^ m * (q : ℂ) ^ (-(m : ℤ))) ^ Nat.log (q ^ 2) (nuAt ϖ B)) := by
  obtain ⟨h, hh, rfl⟩ := hB
  obtain ⟨g, g', d, hgg, hgg', hd, hgd⟩ := GlobalTheory.T.hermitian_matrix_diagonalizable R σ ϖ q ε hR n h hh
  obtain ⟨p, p', e, hpp, hpp', he, hpe⟩ := GlobalTheory.T.hermitian_matrix_diagonalizable R σ ϖ q ε hR m S hS.1
  have hq0 : (q : ℂ) ≠ 0 := by
    have := hR.one_lt
    exact_mod_cast (by omega : q ≠ 0)
  have hunit : ∀ l, e l ∉ lev ϖ 1 := by
    intro l hl
    have h1 : IsUnit p.det := Matrix.isUnit_det_of_right_inverse hpp
    have h2 : IsUnit (cT σ p).det := by
      have : cT σ p * cT σ p' = 1 := by
        have : cT σ (p' * p) = cT σ p * cT σ p' := by
          simp [cT, Matrix.transpose_mul, Matrix.map_mul]
        rw [← this, hpp']
        simp [cT]
      exact Matrix.isUnit_det_of_right_inverse this
    have h3 : IsUnit (Matrix.diagonal e).det := by
      rw [← hpe, Matrix.det_mul, Matrix.det_mul]
      exact (h2.mul hS.2).mul h1
    rw [Matrix.det_diagonal] at h3
    have h4 : IsUnit (e l) := isUnit_of_dvd_unit (Finset.dvd_prod_of_mem _ (Finset.mem_univ l)) h3
    obtain ⟨c, hc⟩ := mem_lev_iff.1 hl
    rw [hc, pow_one] at h4
    exact hR.notUnit (isUnit_of_mul_isUnit_left h4)
  choose eI heI hcard hsum using fun i => GlobalTheory.T.card_range_mul_quotient_bounded_level R σ ϖ q ε hR ψ hψ (fun j a ha ha' => gauss1 hR hψ hε j a ha ha') k (d i) (hd i)
  rw [GlobalTheory.T.matrix_gauss_sum_congr_invariance R σ ϖ hR.fix_ϖ hR.inv k (ψ k) m n h _ g g' S _ p p' hgg hgg' hpp hpp' hgd hpe,
    GlobalTheory.T.matrix_gauss_sum_diagonal_factor R σ ϖ hR.fix_ϖ k (ψ k) m n d e,
    GlobalTheory.T.multiplicity_reduction_diagonal_prod R σ ϖ hR.fix_ϖ hR.inv k n h g g' d hgg hgg' hgd]
  have hq2 : 1 < q ^ 2 := Nat.one_lt_pow (by norm_num) hR.one_lt
  have hnu : (∏ i, Nat.card (Set.range fun w : R ⧸ lev ϖ k => w * Ideal.Quotient.mk (lev ϖ k) (d i))) = (q ^ 2) ^ (∑ i, eI i) := by
    rw [Finset.prod_congr rfl (fun i _ => hcard i), Finset.prod_pow_eq_pow_sum]
  rw [hnu, Nat.log_pow hq2]
  have hM : (Nat.card (Matrix (Fin m) (Fin n) (R ⧸ lev ϖ k)) : ℂ) = ((q : ℂ) ^ (2 * k)) ^ (m * n) := by
    have hc : Nat.card (R ⧸ lev ϖ k) = q ^ (2 * k) := GlobalTheory.T.unramified_quotient_card R σ ϖ q ε hR k
    have : Nat.card (Matrix (Fin m) (Fin n) (R ⧸ lev ϖ k)) = (q ^ (2 * k)) ^ (m * n) := by
      show Nat.card (Fin m → Fin n → R ⧸ lev ϖ k) = _
      rw [Nat.card_fun, Nat.card_fun, hc]
      simp only [Nat.card_eq_fintype_card, Fintype.card_fin]
      rw [← pow_mul, mul_comm n m]
    rw [this]; push_cast; rfl
  rw [hM]
  have hc' : ((ε : ℂ) ^ m * (q : ℂ) ^ (-(m : ℤ))) = ((ε : ℂ) / q) ^ m := by
    rw [div_pow, zpow_neg, zpow_natCast, div_eq_mul_inv]
  rw [hc']
  simp only [fun i l => hsum i (e l) (he l) (hunit l), Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    mul_pow, Finset.prod_mul_distrib]
  rw [← pow_mul, ← pow_mul]
  congr 1
  have hx : ∀ x, (((ε : ℂ) / q) ^ eI x) ^ m = (((ε : ℂ) / q) ^ m) ^ eI x := fun x => by
    rw [← pow_mul, ← pow_mul, mul_comm]
  simp only [hx]
  rw [Finset.prod_pow_eq_pow_sum]

end GlobalTheory.CompanionTheory.SiegLoc
end
