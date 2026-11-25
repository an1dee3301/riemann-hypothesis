module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEval
public import Init.Core
public import Init.Data.Function
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Finsupp.SMul
public import Mathlib.Data.Finsupp.Single
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Prod.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Finsupp.Defs
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.LinearAlgebra.Multilinear.Basic
public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
public import Mathlib.LinearAlgebra.PiTensorProduct.Basis
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic

@[expose] public section

open scoped TensorProduct Matrix Classical

noncomputable section

namespace GlobalTheory.CCRFock

open MvPolynomial

theorem polMap_index_injective (W Λ : Type) [Fintype W] :
    Function.Injective (fun f : W → (Λ →₀ ℕ) => ∑ w, Finsupp.mapDomain (Prod.mk w) (f w)) := by
  have key : ∀ (f : W → (Λ →₀ ℕ)) (w : W) (l : Λ),
      (∑ w, Finsupp.mapDomain (Prod.mk w) (f w)) (w, l) = f w l := by
    intro f w l
    rw [Finsupp.finsetSum_apply, Finset.sum_eq_single w]
    · exact Finsupp.mapDomain_apply_of_injective (Prod.mk_right_injective w) _ _
    · intro v _ hv
      apply Finsupp.mapDomain_notin_range
      rintro ⟨x, hx⟩
      exact hv (congrArg Prod.fst hx)
    · intro h
      exact absurd (Finset.mem_univ w) h
  intro f g h
  funext w
  ext l
  rw [← key f w l, ← key g w l]
  exact congrArg (fun F : (W × Λ) →₀ ℕ => F (w, l)) h

theorem polMap_tprod_monomial (W Λ : Type) [Fintype W] [DecidableEq W] (f : W → (Λ →₀ ℕ)) :
    polMap W Λ (PiTensorProduct.tprod ℂ (fun w => (monomial (f w) (1 : ℂ) : MvPolynomial Λ ℂ))) =
      monomial (∑ w, Finsupp.mapDomain (Prod.mk w) (f w)) 1 := by
  rw [monomial_sum_one]
  simp only [polMap, PiTensorProduct.lift.tprod, MultilinearMap.compLinearMap_apply,
    MultilinearMap.mkPiAlgebra_apply, AlgHom.toLinearMap_apply, rename_monomial]

theorem polMap_injective (W Λ : Type) [Fintype W] [DecidableEq W] :
    Function.Injective (polMap W Λ) := by
  let B := Basis.piTensorProduct (fun _ : W => basisMonomials Λ ℂ)
  have hli : LinearIndependent ℂ (polMap W Λ ∘ B) := by
    have h := (basisMonomials (W × Λ) ℂ).linearIndependent.comp _ (polMap_index_injective W Λ)
    have e : polMap W Λ ∘ B = (basisMonomials (W × Λ) ℂ) ∘
        (fun f : W → (Λ →₀ ℕ) => ∑ w, Finsupp.mapDomain (Prod.mk w) (f w)) := by
      funext f
      simp only [Function.comp, B, Basis.piTensorProduct_apply, coe_basisMonomials]
      exact polMap_tprod_monomial W Λ f
    rw [e]
    exact h
  have h1 : polMap W Λ ∘ₗ Finsupp.linearCombination ℂ B = Finsupp.linearCombination ℂ (polMap W Λ ∘ B) := by
    ext f
    simp
  intro x y hxy
  apply B.repr.injective
  apply hli
  rw [← h1]
  simp only [LinearMap.comp_apply, Module.Basis.linearCombination_repr, hxy]

end GlobalTheory.CCRFock
