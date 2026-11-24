module

public import Mathlib
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.LineKroneckerRightMatrixConjTranspose
public import Formalism.LocalRingCardinality.DataTheta
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Function
public import Init.Data.Nat.Basic
public import Init.Data.NeZero
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.Notation.Pi.Basic
public import Mathlib.Algebra.Order.Kleene
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.Analysis.CStarAlgebra.Module.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Cast.Order.Ring
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Order.Defs.Lattice
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic

@[expose] public section

noncomputable section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial GlobalTheory.JointHarm

namespace GlobalTheory.FischerParts

theorem exists_fockIP (σ : Type) [DecidableEq σ] :
    ∃ ι : MvPolynomial σ ℂ →ₗ[ℂ] lp (fun _ : σ →₀ ℕ => ℂ) 2,
      IsFockIP ι ∧ Function.Injective ι := by
  classical
  let w : (σ →₀ ℕ) → ℕ := fun α => α.prod fun _ k => k.factorial
  have hw : ∀ α, w α ≠ 0 := fun α => Finset.prod_ne_zero_iff.2 fun _ _ => Nat.factorial_ne_zero _
  let v : (σ →₀ ℕ) → lp (fun _ : σ →₀ ℕ => ℂ) 2 := fun α => lp.single 2 α (√(w α) : ℝ)
  have hv : ∀ α β, inner ℂ (v α) (v β) = if α = β then (w α : ℂ) else 0 := by
    intro α β
    simp only [v, lp.inner_single_left, lp.single_apply, Pi.single_apply]
    split_ifs with h
    · subst h
      simp only [RCLike.inner_apply, Complex.conj_ofReal]
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg _), Complex.ofReal_natCast]
    · simp
  refine ⟨(basisMonomials σ ℂ).constr ℂ v, fun α β => ?_, ?_⟩
  · have e : ∀ α, (basisMonomials σ ℂ).constr ℂ v (monomial α 1) = v α := fun α => by
      have := (basisMonomials σ ℂ).constr_basis ℂ v α
      rwa [coe_basisMonomials] at this
    rw [e, e, hv]
    simp [w, Finsupp.prod]
  · refine (basisMonomials σ ℂ).injective_constr_of_linearIndependent ?_
    refine linearIndependent_of_ne_zero_of_inner_eq_zero (fun α h => hw α ?_) fun α β h => ?_
    · have := hv α α
      rw [h, inner_zero_left, if_pos rfl] at this
      exact_mod_cast this.symm
    · exact (hv α β).trans (if_neg h)

theorem fischer_parts : ∀ (p q r s d : ℕ), (homog (Ix p q × Ix r s) (d + 2) = (homog (Ix p q × Ix r s) (d + 2) ⊓ Submodule.span ℂ (harm2 p q r s)) ⊔ Submodule.span ℂ {R | ∃ Q ∈ homog (Ix p q × Ix r s) d, ∃ Z : Mat p q, IsPC Z ∧ R = plusPart (fockAct1 p q r s Z) Q}) ∧ (homog (Ix p q × Ix r s) (d + 2) = (homog (Ix p q × Ix r s) (d + 2) ⊓ Submodule.span ℂ (harm1 p q r s)) ⊔ Submodule.span ℂ {R | ∃ Q ∈ homog (Ix p q × Ix r s) d, ∃ Z : Mat r s, IsPC Z ∧ R = plusPart (fockAct2 p q r s Z) Q}) ∧ (homog (Ix p q × Ix r s) (d + 2) = (homog (Ix p q × Ix r s) (d + 2) ⊓ Submodule.span ℂ (jointHarm p q r s)) ⊔ Submodule.span ℂ {R | ∃ Q ∈ homog (Ix p q × Ix r s) d, (∃ Z : Mat p q, IsPC Z ∧ R = plusPart (fockAct1 p q r s Z) Q) ∨ ∃ Z : Mat r s, IsPC Z ∧ R = plusPart (fockAct2 p q r s Z) Q}) := by
  intro p q r s d
  obtain ⟨ι, hι, hinj⟩ := exists_fockIP (Ln p q r s)
  refine ⟨fischer hι hinj {M | ∃ Z, IsPC Z ∧ M = kron1 r s Z} ?_ ?_ d _ _ (fun P hP => ?_)
      fun P => ?_,
    fischer hι hinj {M | ∃ Z, IsPC Z ∧ M = kron2 p q Z} ?_ ?_ d _ _ (fun P hP => ?_)
      fun P => ?_,
    fischer hι hinj {M | (∃ Z, IsPC Z ∧ M = kron1 r s Z) ∨ ∃ Z, IsPC Z ∧ M = kron2 p q Z}
      ?_ ?_ d _ _ (fun P hP => ?_) fun P => ?_⟩
  · rintro _ ⟨Z, hZ, rfl⟩
    exact odd_kron1 hZ
  · rintro _ ⟨Z, hZ, rfl⟩
    exact ⟨_, ⟨_, isPC_conjTranspose hZ, rfl⟩, lineKroneckerLeftMatrix_conjTranspose Z⟩
  · exact fun Z hZ => hP _ ⟨Z, hZ, rfl⟩
  · constructor
    · rintro ⟨Q, hQ, Z, hZ, rfl⟩
      exact ⟨Q, hQ, _, ⟨Z, hZ, rfl⟩, rfl⟩
    · rintro ⟨Q, hQ, _, ⟨Z, hZ, rfl⟩, rfl⟩
      exact ⟨Q, hQ, Z, hZ, rfl⟩
  · rintro _ ⟨Z, hZ, rfl⟩
    exact odd_kron2 hZ
  · rintro _ ⟨Z, hZ, rfl⟩
    exact ⟨_, ⟨_, isPC_conjTranspose hZ, rfl⟩, lineKroneckerRightMatrix_conjTranspose Z⟩
  · exact fun Z hZ => hP _ ⟨Z, hZ, rfl⟩
  · constructor
    · rintro ⟨Q, hQ, Z, hZ, rfl⟩
      exact ⟨Q, hQ, _, ⟨Z, hZ, rfl⟩, rfl⟩
    · rintro ⟨Q, hQ, _, ⟨Z, hZ, rfl⟩, rfl⟩
      exact ⟨Q, hQ, Z, hZ, rfl⟩
  · rintro _ (⟨Z, hZ, rfl⟩ | ⟨Z, hZ, rfl⟩)
    exacts [odd_kron1 hZ, odd_kron2 hZ]
  · rintro _ (⟨Z, hZ, rfl⟩ | ⟨Z, hZ, rfl⟩)
    exacts [⟨_, .inl ⟨_, isPC_conjTranspose hZ, rfl⟩, lineKroneckerLeftMatrix_conjTranspose Z⟩,
      ⟨_, .inr ⟨_, isPC_conjTranspose hZ, rfl⟩, lineKroneckerRightMatrix_conjTranspose Z⟩]
  · exact ⟨fun Z hZ => hP _ (.inl ⟨Z, hZ, rfl⟩), fun Z hZ => hP _ (.inr ⟨Z, hZ, rfl⟩)⟩
  · constructor
    · rintro ⟨Q, hQ, ⟨Z, hZ, rfl⟩ | ⟨Z, hZ, rfl⟩⟩
      exacts [⟨Q, hQ, _, .inl ⟨Z, hZ, rfl⟩, rfl⟩, ⟨Q, hQ, _, .inr ⟨Z, hZ, rfl⟩, rfl⟩]
    · rintro ⟨Q, hQ, _, ⟨Z, hZ, rfl⟩ | ⟨Z, hZ, rfl⟩, rfl⟩
      exacts [⟨Q, hQ, .inl ⟨Z, hZ, rfl⟩⟩, ⟨Q, hQ, .inr ⟨Z, hZ, rfl⟩⟩]

end GlobalTheory.FischerParts
