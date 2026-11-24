module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIrreducibleSecondFactorOfIrreducibleProduct
public import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsUnitarisableOfCharIff
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Nontrivial.Defs
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Bool.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Associator
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.Order.Notation
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.RepresentationTheory.Subrepresentation
public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Group.Units
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Instances.Matrix

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.CompanionTheory.DegPrinSeries

theorem nontrivial_subrepresentation : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a b : ℕ) (χ₁ χ₂ : kˣ →* ℂˣ), IsSmoothChar χ₁ → IsSmoothChar χ₂ → Nontrivial (Subrepresentation (parInd (two (stdSum (rfl : a + b = a + b))) ((extTensor (detRep (Fin a) χ₁) (detRep (Fin b) χ₂)).comp (leviTwo k (Fin a) (Fin b)).symm.toMonoidHom))) := by
  intro k _ _ _ _ a b χ₁ χ₂ hχ₁ hχ₂
  have hdetChar : ∀ (m : ℕ) (χ : kˣ →* ℂˣ), GlobalTheory.SmGL.IsSmoothChar χ →
      GlobalTheory.PRep.IsSmooth (GlobalTheory.SmGL.detRep (Fin m) χ) := by
    intro m χ hχ
    have hc : Continuous (Matrix.GeneralLinearGroup.det : GL (Fin m) k → kˣ) := by
      rw [Units.continuous_iff]
      constructor
      · have hval : (Units.val ∘ (Matrix.GeneralLinearGroup.det : GL (Fin m) k → kˣ)) =
            fun g : GL (Fin m) k => Matrix.det (g : Matrix (Fin m) (Fin m) k) := by
          funext g
          exact Matrix.GeneralLinearGroup.val_det_apply g
        rw [hval]
        exact Units.continuous_val.matrix_det
      · have hinv : (fun g : GL (Fin m) k => ((Matrix.GeneralLinearGroup.det g)⁻¹ : kˣ).val) =
            fun g => Matrix.det ((g⁻¹ : GL (Fin m) k) : Matrix (Fin m) (Fin m) k) := by
          funext g
          rw [← map_inv, Matrix.GeneralLinearGroup.val_det_apply]
        rw [hinv]
        exact Units.continuous_coe_inv.matrix_det
    unfold GlobalTheory.SmGL.detRep
    rw [GlobalTheory.SmGL.isSmooth_ofChar_iff]
    unfold GlobalTheory.SmGL.IsSmoothChar at hχ ⊢
    exact hc.isOpen_preimage _ hχ
  have hsmooth := GlobalTheory.SmGL.isSmooth_comp
    (GlobalTheory.SmGL.isSmooth_extTensor (hdetChar a χ₁ hχ₁) (hdetChar b χ₂ hχ₂))
    (GlobalTheory.SmGL.leviTwo k (Fin a) (Fin b)).symm.toMonoidHom
    (by exact (continuous_apply Bool.false).prodMk (continuous_apply Bool.true))
  have hu : ((1 : ℂ) ⊗ₜ[ℂ] (1 : ℂ)) ≠ 0 := by
    intro h0
    have := congrArg (TensorProduct.lid ℂ ℂ) h0
    simp at this
  obtain ⟨f, hf1, -⟩ := GlobalTheory.SmGL.ProdIrr.exists_indSp_apply_one
    (GlobalTheory.SmGL.two (GlobalTheory.SmGL.stdSum (rfl : a + b = a + b))) _
    hsmooth ((1 : ℂ) ⊗ₜ[ℂ] (1 : ℂ))
  refine ⟨⟨⟨⊥, fun g ⦃v⦄ hv => ?_⟩, ⟨⊤, fun _ ⦃_⦄ _ => Submodule.mem_top⟩, fun hEq => ?_⟩⟩
  · rw [Submodule.mem_bot] at hv ⊢
    rw [hv, map_zero]
  · have hsub := congrArg Subrepresentation.toSubmodule hEq
    have hf : f = 0 := (Submodule.mem_bot ℂ).1 (Submodule.eq_top_iff'.1 hsub f)
    rw [hf] at hf1
    apply hu
    rw [← hf1]
    first
    | rfl
    | simp

end GlobalTheory.CompanionTheory.DegPrinSeries
end
