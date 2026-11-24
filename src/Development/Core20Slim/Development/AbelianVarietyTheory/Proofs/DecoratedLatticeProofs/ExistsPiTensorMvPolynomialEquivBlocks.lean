module

public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.LatticeFrames.EvalAtOneExtremalMul
public import Init.Classical
public import Init.Core
public import Init.Data.Function
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Ker
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Module.Submodule.LinearMap
public import Mathlib.Algebra.Module.Submodule.Map
public import Mathlib.Algebra.Module.Submodule.Range
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
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Multilinear.Basic
public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
public import Mathlib.LinearAlgebra.PiTensorProduct.Basis
public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic

@[expose] public section

open MvPolynomial Formalism.BasicNotions Formalism.L2.Forms Formalism.L2.Ker GlobalTheory.KJInf MeasureTheory
open scoped TensorProduct

namespace GlobalTheory.BlockPoly

variable (ι σ : Type) [Fintype ι] [DecidableEq ι]

noncomputable def blockMul :
    (ι → MvPolynomial σ ℂ) →ₘₗ[ℂ] MvPolynomial (ι × σ) ℂ :=
  (MultilinearMap.mkPiAlgebra ℂ ι (MvPolynomial (ι × σ) ℂ)).compLinearMap
    (fun τ => (rename (Prod.mk τ) : MvPolynomial σ ℂ →ₐ[ℂ] MvPolynomial (ι × σ) ℂ).toLinearMap)

theorem blockMul_apply (f : ι → MvPolynomial σ ℂ) :
    blockMul ι σ f = ∏ τ, rename (Prod.mk τ) (f τ) := by
  simp [blockMul]

noncomputable def expEquiv : (ι → σ →₀ ℕ) ≃ (ι × σ →₀ ℕ) :=
  Finsupp.equivFunOnFinite.symm.trans Finsupp.curryEquiv.symm

theorem expEquiv_apply (d : ι → σ →₀ ℕ) (a : ι) (b : σ) : expEquiv ι σ d (a, b) = d a b := by
  simp [expEquiv]

theorem sum_mapDomain_eq (d : ι → σ →₀ ℕ) :
    ∑ τ, (d τ).mapDomain (Prod.mk τ) = expEquiv ι σ d := by
  ext ⟨a, b⟩
  rw [expEquiv_apply, Finset.sum_apply', Finset.sum_eq_single a]
  · exact Finsupp.mapDomain_apply_of_injective (fun x y h => by simpa using h) _ _
  · intro τ _ hτ
    apply Finsupp.mapDomain_notin_range
    rintro ⟨c, hc⟩
    exact hτ (congrArg Prod.fst hc)
  · intro h; exact absurd (Finset.mem_univ a) h

theorem prod_rename_monomial (d : ι → σ →₀ ℕ) :
    ∏ τ, rename (Prod.mk τ) (monomial (d τ) (1 : ℂ)) = monomial (expEquiv ι σ d) 1 := by
  simp only [rename_monomial]
  rw [← monomial_sum_one, sum_mapDomain_eq]

noncomputable def blockEquiv :
    PiTensorProduct ℂ (fun _ : ι => MvPolynomial σ ℂ) ≃ₗ[ℂ] MvPolynomial (ι × σ) ℂ :=
  (Basis.piTensorProduct (fun _ : ι => basisMonomials σ ℂ)).equiv
    (basisMonomials (ι × σ) ℂ) (expEquiv ι σ)

theorem blockEquiv_toLinearMap :
    (blockEquiv ι σ).toLinearMap = PiTensorProduct.lift (blockMul ι σ) := by
  refine (Basis.piTensorProduct (fun _ : ι => basisMonomials σ ℂ)).ext (fun p => ?_)
  rw [LinearEquiv.coe_coe, blockEquiv, Module.Basis.equiv_apply, Basis.piTensorProduct_apply,
    PiTensorProduct.lift.tprod, blockMul_apply]
  simp only [coe_basisMonomials]
  rw [prod_rename_monomial]

theorem blockEquiv_tprod (f : ι → MvPolynomial σ ℂ) :
    blockEquiv ι σ (PiTensorProduct.tprod ℂ f) = ∏ τ, rename (Prod.mk τ) (f τ) := by
  rw [← LinearEquiv.coe_coe, blockEquiv_toLinearMap, PiTensorProduct.lift.tprod, blockMul_apply]

theorem map_subtype_injective (U : ι → Submodule ℂ (MvPolynomial σ ℂ)) :
    Function.Injective (PiTensorProduct.map fun τ => (U τ).subtype) := by
  choose g hg using fun τ => LinearMap.exists_leftInverse_of_injective (U τ).subtype (U τ).ker_subtype
  have h : (PiTensorProduct.map g) ∘ₗ (PiTensorProduct.map fun τ => (U τ).subtype) =
      LinearMap.id := by
    rw [← PiTensorProduct.map_comp]
    simp only [hg]
    exact PiTensorProduct.map_id
  exact Function.LeftInverse.injective (g := PiTensorProduct.map g)
    (fun x => by simpa using LinearMap.congr_fun h x)

theorem exists_blockEquiv :
    ∀ (ι σ : Type) [Fintype ι] [DecidableEq ι], ∃ e : PiTensorProduct ℂ (fun _ : ι => MvPolynomial σ ℂ) ≃ₗ[ℂ] MvPolynomial (ι × σ) ℂ, (∀ f : ι → MvPolynomial σ ℂ, e (PiTensorProduct.tprod ℂ f) = ∏ τ, rename (Prod.mk τ) (f τ)) ∧ ∀ U : ι → Submodule ℂ (MvPolynomial σ ℂ), Function.Injective (e.toLinearMap ∘ₗ PiTensorProduct.map fun τ => (U τ).subtype) ∧ LinearMap.range (e.toLinearMap ∘ₗ PiTensorProduct.map fun τ => (U τ).subtype) = Submodule.span ℂ {p | ∃ f : ι → MvPolynomial σ ℂ, (∀ τ, f τ ∈ U τ) ∧ p = ∏ τ, rename (Prod.mk τ) (f τ)} := by
  intro ι σ _ _
  refine ⟨blockEquiv ι σ, blockEquiv_tprod ι σ, fun U => ⟨?_, ?_⟩⟩
  · exact (blockEquiv ι σ).injective.comp (map_subtype_injective ι σ U)
  · rw [LinearMap.range_eq_map, ← PiTensorProduct.span_tprod_eq_top, Submodule.map_span]
    congr 1
    ext p
    constructor
    · rintro ⟨_, ⟨g, rfl⟩, rfl⟩
      refine ⟨fun τ => (g τ : MvPolynomial σ ℂ), fun τ => (g τ).2, ?_⟩
      simp [PiTensorProduct.map_tprod, blockEquiv_tprod]
    · rintro ⟨f, hf, rfl⟩
      refine ⟨PiTensorProduct.tprod ℂ (fun τ => (⟨f τ, hf τ⟩ : U τ)), ⟨_, rfl⟩, ?_⟩
      simp [PiTensorProduct.map_tprod, blockEquiv_tprod]

end GlobalTheory.BlockPoly
