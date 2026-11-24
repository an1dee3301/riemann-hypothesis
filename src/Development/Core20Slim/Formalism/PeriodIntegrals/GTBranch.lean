module

public import Mathlib
public import Formalism.LocalRingCardinality.DataCoeff
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Int.Lemmas
public import Init.Data.Int.Order
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Module.Submodule.Map
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fin.SuccPred
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Block
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.Reindex
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Order.SetNotation
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic

@[expose] public section

noncomputable section

namespace PI

open Formalism.BasicNotions MvPolynomial

def blkHom (R : Type) [CommRing R] (n : ℕ) :
    Matrix (Fin n) (Fin n) R →* Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) R where
  toFun A := Matrix.fromBlocks A 0 0 1
  map_one' := Matrix.fromBlocks_one
  map_mul' A B := by simp [Matrix.fromBlocks_multiply]

def embGL (R : Type) [CommRing R] (n N : ℕ) (h : n + 1 = N) : GL (Fin n) R →* GL (Fin N) R :=
  Units.map (((Matrix.reindexAlgEquiv R R (finSumFinEquiv.trans (finCongr h))).toAlgHom.toRingHom.toMonoidHom).comp
    (blkHom R n))

def Interlace {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) : Prop :=
  ∀ i : Fin n, sg.w i ≤ lam.w ⟨i.1, by omega⟩ ∧ lam.w ⟨i.1 + 1, by omega⟩ ≤ sg.w i

def GTBranch : Prop :=
  ∀ (n N : ℕ) (h : n + 1 = N) (lam : DomWeight N),
    (∀ (mu : DomWeight n) (φ φ' : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ),
      (∀ ψ ∈ ({φ, φ'} : Set _), (∀ s ∈ nablaSq ℂ n mu, ψ s ∈ nablaSq ℂ N lam) ∧
        ∀ (g : GL (Fin n) ℂ), ∀ s ∈ nablaSq ℂ n mu,
          ψ (sqAct ℂ n mu g s) = sqAct ℂ N lam (embGL ℂ n N h g) (ψ s)) →
      (∃ s ∈ nablaSq ℂ n mu, φ' s ≠ 0) →
      Interlace h lam mu ∧ ∃ c : ℂ, ∀ s ∈ nablaSq ℂ n mu, φ s = c • φ' s) ∧
    nablaSq ℂ N lam = ⨆ (mu : DomWeight n) (_ : Interlace h lam mu)
      (φ : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ)
      (_ : (∀ s ∈ nablaSq ℂ n mu, φ s ∈ nablaSq ℂ N lam) ∧
        ∀ (g : GL (Fin n) ℂ), ∀ s ∈ nablaSq ℂ n mu,
          φ (sqAct ℂ n mu g s) = sqAct ℂ N lam (embGL ℂ n N h g) (φ s)), (nablaSq ℂ n mu).map φ

end PI
