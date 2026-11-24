module

public import Mathlib
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.SecondCountableTopologyArchUnitary
public import Development.Core20Slim.GroundTheory.AutomorphicForms.HermitianSpaces
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.MajorantInvolutionDiagonalForm
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Objects
public import Init.Classical
public import Init.Core
public import Init.Data.Function
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Algebra.Star.StarAlgHom
public import Mathlib.Algebra.Star.Unitary
public import Mathlib.Algebra.Star.UnitaryStarAlgAut
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Lattice
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix
open scoped ComplexOrder

noncomputable section

theorem exists_posDef_mul_inv_mul_eq {n : Type*} [Fintype n] [DecidableEq n] {H : Matrix n n ℂ}
    (hH : H.IsHermitian) (hdet : IsUnit H.det) :
    ∃ P : Matrix n n ℂ, P.PosDef ∧ P * H⁻¹ * P = H := by
  set U : Matrix n n ℂ := (hH.eigenvectorUnitary : Matrix n n ℂ) with hUdef
  set d : n → ℝ := hH.eigenvalues with hddef
  have hUU : star U * U = 1 := Unitary.coe_star_mul_self _
  have hUU' : U * star U = 1 := Unitary.coe_mul_star_self _
  have hspec : H = U * diagonal (fun i => ((d i : ℝ) : ℂ)) * star U := by
    have := hH.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at this
    exact this
  have hd : ∀ i, d i ≠ 0 := by
    intro i hi
    have h0 := hdet.ne_zero
    rw [hH.det_eq_prod_eigenvalues] at h0
    exact h0 (Finset.prod_eq_zero (Finset.mem_univ i) (by simp [← hddef, hi]))
  have hinv : H⁻¹ = U * diagonal (fun i => (((d i)⁻¹ : ℝ) : ℂ)) * star U := by
    refine Matrix.inv_eq_right_inv ?_
    rw [hspec]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (star U) U, hUU, Matrix.one_mul, ← Matrix.mul_assoc (diagonal _),
      diagonal_mul_diagonal]
    have : (fun i => ((d i : ℝ) : ℂ) * (((d i)⁻¹ : ℝ) : ℂ)) = fun _ => (1 : ℂ) := by
      funext i
      rw [← Complex.ofReal_mul, mul_inv_cancel₀ (hd i), Complex.ofReal_one]
    rw [this, diagonal_one, Matrix.one_mul, hUU']
  refine ⟨U * diagonal (fun i => ((|d i| : ℝ) : ℂ)) * star U, ?_, ?_⟩
  · have hD : (diagonal (fun i => ((|d i| : ℝ) : ℂ))).PosDef :=
      Matrix.posDef_diagonal_iff.mpr fun i => Complex.zero_lt_real.mpr (abs_pos.mpr (hd i))
    have hinj : Function.Injective U.vecMul := by
      intro x y hxy
      have := congrArg (fun z => z ᵥ* star U) hxy
      simpa only [vecMul_vecMul, hUU', vecMul_one] using this
    simpa only [star_eq_conjTranspose] using hD.mul_mul_conjTranspose_same hinj
  · rw [hinv]
    conv_rhs => rw [hspec]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (star U) U, hUU, Matrix.one_mul, ← Matrix.mul_assoc (star U) U, hUU,
      Matrix.one_mul, ← Matrix.mul_assoc (diagonal _) (diagonal _), diagonal_mul_diagonal,
      ← Matrix.mul_assoc (diagonal _) (diagonal _), diagonal_mul_diagonal]
    congr 3
    funext i
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul]
    congr 1
    calc |d i| * (d i)⁻¹ * |d i| = |d i| * |d i| * (d i)⁻¹ := by ring
      _ = d i * d i * (d i)⁻¹ := by rw [abs_mul_abs_self]
      _ = d i := mul_inv_cancel_right₀ (hd i) _

section Spaces

variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem MajorantExists.proof (h : HermitianForm F E W) (v : Basis ι E W)
    (h₁ : GramAtData.Statement h v) : MajorantExists.Statement h v := by
  choose P hP hPH using fun w => exists_posDef_mul_inv_mul_eq (h₁ w).1 (h₁ w).2
  exact ⟨⟨P, hP, hPH⟩⟩

end Spaces

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
