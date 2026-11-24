module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Block
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Logic.Equiv.Fin.Basic

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.LeviUnitary

open Matrix

section Ring

variable {R : Type} [CommRing R] {n m : ℕ} {ι : Matrix (Fin n) (Fin m) R} {π : Matrix (Fin m) (Fin n) R}



end Ring

theorem det_ne_zero_of_hasSig {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : HasSig M r s) : M.det ≠ 0 := by
  obtain ⟨rfl, A, hA⟩ := h
  intro h0
  let A' : Matrix (Fin (r + s)) (Fin (r + s)) ℂ := A.submatrix id finSumFinEquiv.symm
  have h1 : A'ᵀ * M * A'.map star = (Matrix.fromBlocks 1 0 0 (-1) : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ).submatrix
      finSumFinEquiv.symm finSumFinEquiv.symm := by
    rw [← hA]; ext i j; simp [A', Matrix.mul_apply]
  have h2 := congrArg Matrix.det h1
  rw [det_mul, det_mul, h0, det_submatrix_equiv_self, det_fromBlocks_zero₂₁, det_one, det_neg, det_one] at h2
  simp at h2
  exact absurd h2.symm (by simp)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}






end GlobalTheory.LeviUnitary

end
