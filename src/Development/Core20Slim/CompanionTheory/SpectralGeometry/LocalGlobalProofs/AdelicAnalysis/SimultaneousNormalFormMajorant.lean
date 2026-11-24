module

public import Development.Core20Slim.CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Ring.Commute
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.Real.Star
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.PartialOrder

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

namespace GlobalTheory.CompanionTheory.SW.Diag


open scoped MatrixOrder in
theorem exists_eq_transpose_mul_self {ι : Type} [Fintype ι] [DecidableEq ι]
    {T : Matrix ι ι ℝ} (hT : T.PosSemidef) : ∃ B : Matrix ι ι ℝ, T = Bᵀ * B := by
  have hH := hT.isHermitian
  set U : Matrix ι ι ℝ := (hH.eigenvectorUnitary : Matrix ι ι ℝ) with hUdef
  have hspec : T = U * diagonal (RCLike.ofReal ∘ hH.eigenvalues) * star U := hH.spectral_theorem
  have hstar : star U = Uᵀ := by
    rw [Matrix.star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]
  rw [hstar] at hspec
  have hd : diagonal (RCLike.ofReal ∘ hH.eigenvalues) =
      diagonal (fun i => Real.sqrt (hH.eigenvalues i)) *
        diagonal (fun i => Real.sqrt (hH.eigenvalues i)) := by
    rw [diagonal_mul_diagonal]
    congr 1
    funext i
    exact (Real.mul_self_sqrt (hT.eigenvalues_nonneg i)).symm
  refine ⟨diagonal (fun i => Real.sqrt (hH.eigenvalues i)) * Uᵀ, ?_⟩
  rw [transpose_mul, transpose_transpose, diagonal_transpose]
  conv_lhs => rw [hspec, hd]
  simp only [Matrix.mul_assoc]

theorem simultaneous_normal_form_majorant :
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (S P : Matrix ι ι ℝ), S.IsSymm → S.det ≠ 0 →
      P.PosDef → P * S⁻¹ * P = S →
      ∃ (g : Matrix ι ι ℝ) (e : ι → ℝ), g.det ≠ 0 ∧ (∀ i, e i = 1 ∨ e i = -1) ∧
        gᵀ * P * g = 1 ∧ gᵀ * S * g = Matrix.diagonal e := by
  intro ι _ _ S P hS hSdet hP hPS
  obtain ⟨B, hB⟩ := exists_eq_transpose_mul_self hP.posSemidef
  have hPdet : P.det ≠ 0 := hP.det_pos.ne'
  have hBdet : B.det ≠ 0 := by
    intro h
    apply hPdet
    rw [hB, det_mul, det_transpose, h, mul_zero]
  have hBu : IsUnit B.det := isUnit_iff_ne_zero.mpr hBdet
  have hSu : IsUnit S.det := isUnit_iff_ne_zero.mpr hSdet
  have hPu : IsUnit P.det := isUnit_iff_ne_zero.mpr hPdet
  set C := B⁻¹ with hCdef
  have hBC : B * C = 1 := mul_nonsing_inv B hBu
  have hCB : C * B = 1 := nonsing_inv_mul B hBu
  have hCPC : Cᵀ * P * C = 1 := by
    rw [hB]
    calc Cᵀ * (Bᵀ * B) * C = (B * C)ᵀ * (B * C) := by
          rw [transpose_mul]
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hBC, transpose_one, Matrix.one_mul]
  have hPCC : P * (C * Cᵀ) = 1 := by
    rw [hB]
    calc Bᵀ * B * (C * Cᵀ) = Bᵀ * ((B * C) * Cᵀ) := by simp only [Matrix.mul_assoc]
      _ = (C * B)ᵀ := by rw [hBC, Matrix.one_mul, transpose_mul]
      _ = 1 := by rw [hCB, transpose_one]
  have hCC : C * Cᵀ = P⁻¹ := (inv_eq_right_inv hPCC).symm
  have hSPS : S * P⁻¹ * S = P := by
    calc S * P⁻¹ * S = P * S⁻¹ * P * P⁻¹ * S := by rw [hPS]
      _ = P * S⁻¹ * (P * P⁻¹) * S := by simp only [Matrix.mul_assoc]
      _ = P := by
          rw [mul_nonsing_inv P hPu, Matrix.mul_one, Matrix.mul_assoc, nonsing_inv_mul S hSu,
            Matrix.mul_one]
  set A := Cᵀ * S * C with hAdef
  have hAT : Aᵀ = A := by
    simp only [hAdef, transpose_mul, transpose_transpose, hS.eq, Matrix.mul_assoc]
  have hA : A.IsHermitian := by
    unfold IsHermitian
    rw [conjTranspose_eq_transpose_of_trivial]
    exact hAT
  have hA2 : A * A = 1 := by
    calc A * A = Cᵀ * (S * (C * Cᵀ) * S) * C := by simp only [hAdef, Matrix.mul_assoc]
      _ = 1 := by rw [hCC, hSPS, hCPC]
  set U : Matrix ι ι ℝ := (hA.eigenvectorUnitary : Matrix ι ι ℝ) with hUdef
  set e : ι → ℝ := RCLike.ofReal ∘ hA.eigenvalues with hedef
  have hspec : A = U * diagonal e * star U := hA.spectral_theorem
  have hU1 : star U * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hA.eigenvectorUnitary.2
  have hU2 : U * star U = 1 := Matrix.mem_unitaryGroup_iff.mp hA.eigenvectorUnitary.2
  have hstar : star U = Uᵀ := by
    rw [Matrix.star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]
  rw [hstar] at hspec hU1 hU2
  have hD : Uᵀ * A * U = diagonal e := by
    rw [hspec]
    calc Uᵀ * (U * diagonal e * Uᵀ) * U = (Uᵀ * U) * diagonal e * (Uᵀ * U) := by
          simp only [Matrix.mul_assoc]
      _ = diagonal e := by rw [hU1, Matrix.one_mul, Matrix.mul_one]
  have hDD : diagonal e * diagonal e = 1 := by
    rw [← hD]
    calc Uᵀ * A * U * (Uᵀ * A * U) = Uᵀ * (A * (U * Uᵀ) * A) * U := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hU2, Matrix.mul_one, hA2, Matrix.mul_one, hU1]
  have he : ∀ i, e i = 1 ∨ e i = -1 := by
    intro i
    have h := congrFun (congrFun hDD i) i
    rw [diagonal_mul_diagonal, diagonal_apply_eq, one_apply_eq] at h
    exact mul_self_eq_one_iff.mp h
  refine ⟨C * U, e, ?_, he, ?_, ?_⟩
  · rw [det_mul]
    refine mul_ne_zero ?_ ?_
    · intro h
      have h' := congrArg det hCB
      rw [det_mul, h, zero_mul, det_one] at h'
      exact zero_ne_one h'
    · intro h
      have h' := congrArg det hU1
      rw [det_mul, h, mul_zero, det_one] at h'
      exact zero_ne_one h'
  · calc (C * U)ᵀ * P * (C * U) = Uᵀ * (Cᵀ * P * C) * U := by
          rw [transpose_mul]
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hCPC, Matrix.mul_one, hU1]
  · calc (C * U)ᵀ * S * (C * U) = Uᵀ * A * U := by
          rw [transpose_mul]
          simp only [hAdef, Matrix.mul_assoc]
      _ = diagonal e := hD

end GlobalTheory.CompanionTheory.SW.Diag
