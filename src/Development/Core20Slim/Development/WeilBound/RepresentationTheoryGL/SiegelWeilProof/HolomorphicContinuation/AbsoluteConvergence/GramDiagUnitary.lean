module

public import Mathlib
public import Batteries.Logic
public import Init.ByCases
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.GroupWithZero.Units.Lemmas
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Algebra.Star.StarAlgHom
public import Mathlib.Algebra.Star.Unitary
public import Mathlib.Algebra.Star.UnitaryStarAlgAut
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.Analysis.CStarAlgebra.Module.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.InnerProductSpace.Orthonormal
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.Analysis.Normed.Lp.WithLp
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Operator.LinearIsometry
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.CoeSort
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Restrict
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Matrix.Basis
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.RingTheory.Bialgebra.Basic
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.Tactic.FieldSimp.Lemmas

@[expose] public section

open scoped Matrix

namespace PositivityTheory.Rg.Sw.KAKA

open Matrix

theorem gram_diag_unitary {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (s : Fin n → ℝ)
    (hM : Mᴴ * M = diagonal (fun j => ((s j ^ 2 : ℝ) : ℂ))) :
    ∃ U : Matrix (Fin n) (Fin n) ℂ, Uᴴ * U = 1 ∧ M = U * diagonal (fun j => (s j : ℂ)) := by
  classical
  let c : Fin n → EuclideanSpace ℂ (Fin n) := fun j => WithLp.toLp 2 (fun i => M i j)
  have hin : ∀ j k, inner ℂ (c j) (c k) = (Mᴴ * M) j k := by
    intro j k
    rw [EuclideanSpace.inner_toLp_toLp, dotProduct]
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, mul_comm]
  let v : Fin n → EuclideanSpace ℂ (Fin n) := fun j => ((s j : ℂ)⁻¹) • c j
  let S : Set (Fin n) := {j | s j ≠ 0}
  have hv : Orthonormal ℂ (S.restrict v) := by
    rw [orthonormal_iff_ite]
    rintro ⟨j, hj⟩ ⟨k, hk⟩
    change inner ℂ (v j) (v k) = _
    simp only [v, inner_smul_left, inner_smul_right, hin, hM, Matrix.diagonal_apply]
    by_cases hjk : j = k
    · subst hjk
      have hj' : (s j : ℂ) ≠ 0 := by exact_mod_cast hj
      simp only [if_true]
      rw [Complex.ofReal_pow, map_inv₀, Complex.conj_ofReal]
      field_simp
    · have : (⟨j, hj⟩ : S) ≠ ⟨k, hk⟩ := fun h => hjk (congrArg Subtype.val h)
      simp [hjk]
  obtain ⟨b, hb⟩ := hv.exists_orthonormalBasis_extension_of_card_eq (by simp)
  have hU := (EuclideanSpace.basisFun (Fin n) ℂ).toMatrix_orthonormalBasis_mem_unitary b
  set U := (EuclideanSpace.basisFun (Fin n) ℂ).toBasis.toMatrix b with hUd
  refine ⟨U, ?_, ?_⟩
  · have := Matrix.mem_unitaryGroup_iff'.mp hU
    simpa [Matrix.star_eq_conjTranspose] using this
  · have hUe : ∀ i j, U i j = (b j).ofLp i := by
      intro i j
      simp [hUd, Module.Basis.toMatrix_apply]
    ext i j
    rw [Matrix.mul_diagonal, hUe]
    by_cases hj : s j = 0
    · have hc : c j = 0 := by
        have h1 := hin j j
        rw [hM, Matrix.diagonal_apply_eq, hj] at h1
        simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Complex.ofReal_zero] at h1
        exact inner_self_eq_zero.mp h1
      have : M i j = 0 := by
        have := congrArg (fun x : EuclideanSpace ℂ (Fin n) => x.ofLp i) hc
        simpa [c] using this
      rw [this, hj]; simp
    · have hbj : b j = v j := hb j hj
      rw [hbj]
      have hj' : (s j : ℂ) ≠ 0 := by exact_mod_cast hj
      simp only [v, c, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
      field_simp

theorem gram_eigen {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    ∃ (W : Matrix (Fin n) (Fin n) ℂ) (l : Fin n → ℝ), Wᴴ * W = 1 ∧ W * Wᴴ = 1 ∧
      (A * W)ᴴ * (A * W) = diagonal (fun j => (l j : ℂ)) := by
  have hG : (Aᴴ * A).IsHermitian := Matrix.isHermitian_conjTranspose_mul_self A
  have hdiag := hG.conjStarAlgAut_star_eigenvectorUnitary
  rw [Unitary.conjStarAlgAut_star_apply] at hdiag
  refine ⟨(hG.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ), hG.eigenvalues, ?_, ?_, ?_⟩
  · have := Matrix.mem_unitaryGroup_iff'.mp hG.eigenvectorUnitary.2
    simpa [Matrix.star_eq_conjTranspose] using this
  · have := Matrix.mem_unitaryGroup_iff.mp hG.eigenvectorUnitary.2
    simpa [Matrix.star_eq_conjTranspose] using this
  · rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Aᴴ, ← Matrix.mul_assoc, ← Matrix.star_eq_conjTranspose,
      hdiag]
    rfl

end PositivityTheory.Rg.Sw.KAKA
