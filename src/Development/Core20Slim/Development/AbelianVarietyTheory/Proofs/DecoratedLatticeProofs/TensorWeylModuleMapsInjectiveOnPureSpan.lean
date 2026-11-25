module

public import Mathlib
public import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormalizedFockFormPureTensorProperties
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FlagMeasures.TensorTypesRealPlacesEquivSpanWeylModules
public import Formalism.LocalRingCardinality.DataCoeff
public import Init.BinderNameHint
public import Init.Classical
public import Init.Core
public import Init.Data.Function
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Ker
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Module.Submodule.Map
public import Mathlib.Algebra.Module.Submodule.Range
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Finsupp.SMul
public import Mathlib.Data.Finsupp.Single
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Multilinear.Basic
public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
public import Mathlib.LinearAlgebra.PiTensorProduct.Basis
public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.Tactic.Push

@[expose] public section

open Formalism.BasicNotions Formalism.L2.Forms
open scoped TensorProduct

namespace GlobalTheory.TenInj

noncomputable def tenMap {ι : Type} [Fintype ι] {n : ℕ} {V : ι → Type} [∀ τ, AddCommGroup (V τ)] [∀ τ, Module ℂ (V τ)]
    (j : ∀ τ, V τ →ₗ[ℂ] MvPolynomial (Fin n × Fin n) ℂ) :
    (⨂[ℂ] τ, V τ) →ₗ[ℂ] MvPolynomial (ι × Fin n × Fin n) ℂ :=
  PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra ℂ ι (MvPolynomial (ι × Fin n × Fin n) ℂ)).compLinearMap
    (fun τ => (MvPolynomial.rename (Prod.mk τ)).toLinearMap ∘ₗ j τ))

theorem tenMap_tprod {ι : Type} [Fintype ι] {n : ℕ} {V : ι → Type} [∀ τ, AddCommGroup (V τ)] [∀ τ, Module ℂ (V τ)]
    (j : ∀ τ, V τ →ₗ[ℂ] MvPolynomial (Fin n × Fin n) ℂ) (x : ∀ τ, V τ) :
    tenMap j (PiTensorProduct.tprod ℂ x) = ten (fun τ => j τ (x τ)) := by
  unfold tenMap ten
  rw [PiTensorProduct.lift.tprod, MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply]
  rfl

theorem nfAll_zero_left {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n)
    (q : MvPolynomial (ι × Fin n × Fin n) ℂ) : nfAll lam 0 q = 0 := by
  have h := GlobalTheory.TenTypes.nfAll_smul_left lam 0 0 q
  simpa using h

theorem main : ∀ (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n) (V : ι → Type) [∀ τ, AddCommGroup (V τ)] [∀ τ, Module ℂ (V τ)] (j : ∀ τ, V τ →ₗ[ℂ] MvPolynomial (Fin n × Fin n) ℂ) (d : ι → ℕ) (b : ∀ τ, Module.Basis (Fin (d τ)) ℂ (V τ)), (∀ τ ξ, j τ ξ ∈ delSq ℂ n (lam τ)) → (∀ τ, ∀ p ∈ delSq ℂ n (lam τ), ∃ ξ, j τ ξ = p) → (∀ τ a a', normFock (lam τ) (j τ (b τ a)) (j τ (b τ a')) = if a = a' then 1 else 0) → ∃ Jt : (⨂[ℂ] τ, V τ) →ₗ[ℂ] MvPolynomial (ι × Fin n × Fin n) ℂ, Function.Injective Jt ∧ LinearMap.range Jt = CSpan lam ∧ ∀ x : (∀ τ, V τ), Jt (PiTensorProduct.tprod ℂ x) = ten (fun τ => j τ (x τ)) := by
  intro ι _ n lam V _ _ j d b hin hon hortho
  refine ⟨tenMap j, ?_, ?_, tenMap_tprod j⟩
  ·
    let B := Basis.piTensorProduct b
    have hB : ∀ i, B i = PiTensorProduct.tprod ℂ (fun τ => b τ (i τ)) := fun i => Basis.piTensorProduct_apply b i
    obtain ⟨hprod, -, -⟩ := GlobalTheory.FockTen.nfAll_ten ι n lam
    have hpair : ∀ i i', nfAll lam (tenMap j (B i)) (tenMap j (B i')) = if i = i' then 1 else 0 := by
      intro i i'
      rw [hB, hB, tenMap_tprod, tenMap_tprod, hprod]
      simp_rw [hortho]
      by_cases h : i = i'
      · subst h; simp
      · rw [if_neg h]
        obtain ⟨τ, hτ⟩ : ∃ τ, i τ ≠ i' τ := by
          by_contra hc; push_neg at hc; exact h (funext hc)
        exact Finset.prod_eq_zero (Finset.mem_univ τ) (if_neg hτ)
    have hcoord : ∀ i' x, nfAll lam (tenMap j x) (tenMap j (B i')) = B.coord i' x := by
      intro i'
      let L : (⨂[ℂ] τ, V τ) →ₗ[ℂ] ℂ :=
        { toFun := fun x => nfAll lam (tenMap j x) (tenMap j (B i'))
          map_add' := fun x y => by rw [map_add (f := _), GlobalTheory.TenTypes.nfAll_add_left]
          map_smul' := fun c x => by rw [map_smul, GlobalTheory.TenTypes.nfAll_smul_left]; rfl }
      have hL : L = B.coord i' := by
        refine B.ext fun i => ?_
        show nfAll lam (tenMap j (B i)) (tenMap j (B i')) = B.coord i' (B i)
        rw [hpair, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
      intro x
      exact LinearMap.congr_fun hL x
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    refine B.ext_elem fun i' => ?_
    rw [map_zero, Finsupp.zero_apply, ← Module.Basis.coord_apply, ← hcoord, hx, nfAll_zero_left]
  ·
    rw [LinearMap.range_eq_map, ← PiTensorProduct.span_tprod_eq_top, Submodule.map_span]
    unfold CSpan
    congr 1
    ext p
    constructor
    · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨fun τ => j τ (x τ), fun τ => hin τ _, tenMap_tprod j x⟩
    · rintro ⟨f, hf, rfl⟩
      choose ξ hξ using fun τ => hon τ (f τ) (hf τ)
      refine ⟨PiTensorProduct.tprod ℂ ξ, ⟨ξ, rfl⟩, ?_⟩
      rw [tenMap_tprod]
      congr 1
      funext τ
      exact hξ τ

end GlobalTheory.TenInj
