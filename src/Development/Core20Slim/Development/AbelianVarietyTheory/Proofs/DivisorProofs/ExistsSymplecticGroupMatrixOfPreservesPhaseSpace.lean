module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPairingStdP
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Sum.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Opposite
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Opposite
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Basic
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Opposites
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.Real.Star
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Block
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.SymplecticGroup
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Lattice
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

open scoped SchwartzMap Matrix

namespace GlobalTheory

open Matrix

theorem sympl_eq_neg_dotProduct_J {l : Type} [Fintype l] [DecidableEq l] (w w' : l ⊕ l → ℝ) :
    GlobalTheory.RealWeil.sympl w w' = -(w ⬝ᵥ (J l ℝ *ᵥ w')) := by
  simp only [GlobalTheory.RealWeil.sympl, GlobalTheory.RealWeil.pPart, GlobalTheory.RealWeil.qPart, J, EuclideanSpace.inner_eq_star_dotProduct]
  simp [dotProduct, Fintype.sum_sum_type, fromBlocks_mulVec, Matrix.one_apply, Finset.sum_neg_distrib, mul_comm, Matrix.neg_mulVec, Matrix.one_mulVec]
  ring

theorem exists_symplecticGroup_of_sympl (l : Type) [Fintype l] [DecidableEq l]
    (ψ : (l ⊕ l → ℝ) →ₗ[ℝ] (l ⊕ l → ℝ))
    (h : ∀ w w', GlobalTheory.RealWeil.sympl (ψ w) (ψ w') = GlobalTheory.RealWeil.sympl w w') :
    ∃ M : Matrix.symplecticGroup l ℝ, ∀ w, (M : Matrix (l ⊕ l) (l ⊕ l) ℝ) *ᵥ w = ψ w := by
  set M := LinearMap.toMatrix' ψ with hM
  have hMv : ∀ w, M *ᵥ w = ψ w := fun w => by rw [hM, LinearMap.toMatrix'_mulVec]
  have key : ∀ w w', w ⬝ᵥ ((Mᵀ * J l ℝ * M) *ᵥ w') = w ⬝ᵥ (J l ℝ *ᵥ w') := by
    intro w w'
    have := h w w'
    rw [sympl_eq_neg_dotProduct_J, sympl_eq_neg_dotProduct_J, ← hMv, ← hMv] at this
    rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]
    linarith
  have hmem : M ∈ Matrix.symplecticGroup l ℝ := by
    rw [SymplecticGroup.mem_iff']
    ext i j
    have := key (Pi.single i 1) (Pi.single j 1)
    simpa [single_dotProduct, mulVec_single] using this
  exact ⟨⟨M, hmem⟩, hMv⟩

end GlobalTheory
