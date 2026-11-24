module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdMinorsMemInv
public import Init.ByCases
public import Init.Core
public import Init.Data.Zero
public import Init.Ext
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Submodule.LinearMap
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Basic
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.IsEmpty.Defs
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Logic.Function.Basic
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic

@[expose] public section

noncomputable section

open MvPolynomial

namespace GlobalTheory.ColLie

open GlobalTheory.MinorFrame

variable {ι : Type} [DecidableEq ι]

def colDer {d a : ℕ} (τ : ι) (S : Matrix (Fin a) (Fin a) ℂ) : Module.End ℂ (Pol ι d a) :=
  ∑ i : Fin d, ∑ j : Fin a, ∑ k : Fin a,
    S k j • (LinearMap.mulLeft ℂ (X (τ, i, k) : Pol ι d a) ∘ₗ (pderiv (τ, i, j)).toLinearMap)

def atPl {a : ℕ} (τ : ι) (g : Matrix (Fin a) (Fin a) ℂ) : ι → Matrix (Fin a) (Fin a) ℂ :=
  Function.update 1 τ g

theorem colDer_apply {d a : ℕ} (τ : ι) (S : Matrix (Fin a) (Fin a) ℂ) (P : Pol ι d a) :
    colDer τ S P = ∑ i : Fin d, ∑ j : Fin a, ∑ k : Fin a, S k j • (X (τ, i, k) * pderiv (τ, i, j) P) := by
  simp [colDer, LinearMap.sum_apply]

theorem colDer_X {d a : ℕ} (τ : ι) (S : Matrix (Fin a) (Fin a) ℂ) (v : Var ι d a) :
    colDer (d := d) τ S (X v) = if v.1 = τ then ∑ k, S k v.2.2 • (X (τ, v.2.1, k) : Pol ι d a) else 0 := by
  obtain ⟨σ, i₀, j₀⟩ := v
  rw [colDer_apply]
  simp only [pderiv_X, Pi.single_apply, Prod.ext_iff]
  by_cases h : σ = τ
  · subst h
    simp only [if_true]
    rw [Finset.sum_eq_single i₀, Finset.sum_eq_single j₀]
    · simp
    · intro j _ hj
      simp [Ne.symm hj]
    · simp
    · intro i _ hi
      simp [Ne.symm hi]
    · simp
  · simp [h, Ne.symm h]

end GlobalTheory.ColLie

end
