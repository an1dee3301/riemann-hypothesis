module

public import Mathlib
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Int.Lemmas
public import Init.Data.Int.Order
public import Init.Data.List.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.IsApply
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Order.Nat
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

namespace GlobalTheory.Chain.RealIt

open MvPolynomial

theorem totalDegree_mulLeft_add {σ : Type} (Q : MvPolynomial σ ℂ)
    (L : Module.End ℂ (MvPolynomial σ ℂ)) (hQ : Q ≠ 0) (hh : Q.IsHomogeneous 2)
    (hL : ∀ P, (L P).totalDegree ≤ P.totalDegree) (φ : MvPolynomial σ ℂ) (hφ : φ ≠ 0) :
    ((LinearMap.mulLeft ℂ Q + L) φ).totalDegree = φ.totalDegree + 2 := by
  have h1 : (Q * φ).totalDegree = φ.totalDegree + 2 := by
    rw [totalDegree_mul_of_isDomain hQ hφ, hh.totalDegree hQ, add_comm]
  have h2 : (L φ).totalDegree < (Q * φ).totalDegree := by
    have := hL φ
    omega
  rw [LinearMap.add_apply, LinearMap.mulLeft_apply, totalDegree_add_eq_left_of_totalDegree_lt h2, h1]

theorem exists_totalDegree_le_of_finiteDimensional {σ : Type} (F : Submodule ℂ (MvPolynomial σ ℂ))
    (hF : FiniteDimensional ℂ F) : ∃ N : ℕ, ∀ P ∈ F, P.totalDegree ≤ N := by
  obtain ⟨s, hs⟩ : F.FG := (Submodule.fg_iff_finiteDimensional F).2 hF
  refine ⟨s.sup totalDegree, fun P hP => ?_⟩
  have hle : F ≤ restrictTotalDegree σ ℂ (s.sup totalDegree) := by
    rw [← hs, Submodule.span_le]
    intro x hx
    exact (mem_restrictTotalDegree σ _ x).2 (Finset.le_sup (f := totalDegree) hx)
  exact (mem_restrictTotalDegree σ _ P).1 (hle hP)

theorem not_locallyFinite_mulLeft_add :
    ∀ (σ : Type) [Finite σ] (Q : MvPolynomial σ ℂ) (L : Module.End ℂ (MvPolynomial σ ℂ)),
      Q ≠ 0 → Q.IsHomogeneous 2 → (∀ P, (L P).totalDegree ≤ P.totalDegree) →
      ∀ φ : MvPolynomial σ ℂ, φ ≠ 0 → ∀ F : Submodule ℂ (MvPolynomial σ ℂ),
        FiniteDimensional ℂ F → ¬ ∀ n : ℕ, ((LinearMap.mulLeft ℂ Q + L) ^ n) φ ∈ F := by
  intro σ _ Q L hQ hh hL φ hφ F hF hall
  obtain ⟨N, hN⟩ := exists_totalDegree_le_of_finiteDimensional F hF
  have key : ∀ n : ℕ, ((LinearMap.mulLeft ℂ Q + L) ^ n) φ ≠ 0 ∧
      (((LinearMap.mulLeft ℂ Q + L) ^ n) φ).totalDegree = φ.totalDegree + 2 * n := by
    intro n
    induction n with
    | zero => simpa using hφ
    | succ n ih =>
      have h := totalDegree_mulLeft_add Q L hQ hh hL _ ih.1
      rw [pow_succ', Module.End.mul_apply]
      refine ⟨fun h0 => ?_, by rw [h, ih.2]; ring⟩
      rw [h0, totalDegree_zero] at h
      omega
  have h1 := hN _ (hall (N + 1))
  rw [(key (N + 1)).2] at h1
  omega

end GlobalTheory.Chain.RealIt
