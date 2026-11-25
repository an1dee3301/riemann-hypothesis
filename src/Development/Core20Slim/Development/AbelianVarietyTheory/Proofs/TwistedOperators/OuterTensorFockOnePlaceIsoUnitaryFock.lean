module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NonemptyInvFunEquiv
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPiTensorMvPolynomialProdEquiv
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.MinorOrderedEntries
public import Formalism.GradedWeylDivisibility.StatementA
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Matrix.Mul
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Mathlib.LinearAlgebra.Multilinear.Basic
public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic

@[expose] public section

open MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.OneFunctional Formalism.BasicNotions GlobalTheory.Branching
open scoped TensorProduct DirectSum Kronecker Matrix

namespace GlobalTheory.OneFunctional.FockTensor

theorem linSub_prod {ι σ : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ] (M : ι → Matrix σ σ ℂ)
    (f : ι → MvPolynomial (ι × σ) ℂ) : linSub M (∏ τ, f τ) = ∏ τ, linSub M (f τ) := by
  simp only [linSub, MonoidHom.coe_mk, OneHom.coe_mk, AlgHom.toLinearMap_apply, map_prod]

theorem linSub_rename {ι σ : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ] (M : ι → Matrix σ σ ℂ)
    (τ : ι) (f : MvPolynomial σ ℂ) :
    linSub M (rename (Prod.mk τ) f) = rename (Prod.mk τ) (Formalism.GradedWeylDivisibility.sub (M τ)ᵀ f) := by
  unfold Formalism.GradedWeylDivisibility.sub
  simp only [linSub, MonoidHom.coe_mk, OneHom.coe_mk, AlgHom.toLinearMap_apply, aeval_rename]
  rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
  congr 1
  congr 1
  funext i
  set_option synthInstance.maxHeartbeats 100000 in
    simp [Function.comp_apply, map_sum, Matrix.transpose_apply]

theorem fockOne_apply (a b : ℕ) (α β : ℤ) (h : U a) (g : U b) (f : MvPolynomial (Fin b × Fin a) ℂ) :
    fockOne a b α β (h, g) f =
      ((detU a h ^ α * detU b g ^ β : ℂˣ) : ℂ) • Formalism.GradedWeylDivisibility.sub (g.1 ⊗ₖ (star h.1)ᵀ)ᵀ f := rfl

theorem fock_apply {ι : Type} [Fintype ι] [DecidableEq ι] (a b : ℕ) (α β : ι → ℤ) (h : UG ι a) (g : UG ι b)
    (f : Pol ι a b) :
    fock a b α β (h, g) f =
      (((∏ τ, detU a (h τ) ^ α τ) * ∏ τ, detU b (g τ) ^ β τ : ℂˣ) : ℂ) •
        linSub (fun τ => (g τ).1 ⊗ₖ (star (h τ).1)ᵀ) f := rfl

theorem outer₂_fockOne_iso : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (a b : ℕ) (α β : ι → ℤ),
    Iso (outer₂ fun τ => fockOne a b (α τ) (β τ)) (fock a b α β) := by
  intro ι _ _ a b α β
  obtain ⟨e, he⟩ := GlobalTheory.PolyTensor.exists_piTensor_equiv ι (Fin b × Fin a)
  refine ⟨e, ?_⟩
  rintro ⟨h, g⟩ x
  have key : e.toLinearMap ∘ₗ outer₂ (fun τ => fockOne a b (α τ) (β τ)) (h, g) =
      fock a b α β (h, g) ∘ₗ e.toLinearMap := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro f
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
      outer₂_apply, PiTensorProduct.map_tprod, he, fockOne_apply, fock_apply, linSub_prod, linSub_rename]
    simp only [map_smul]
    simp only [Algebra.smul_def, Finset.prod_mul_distrib, ← map_prod, Units.coe_prod, Units.val_mul]
  exact LinearMap.congr_fun key x

end GlobalTheory.OneFunctional.FockTensor
