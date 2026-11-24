module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Init.Core
public import Init.Data.Sum.Basic
public import Init.Data.Sum.Lemmas
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Support
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.SProd
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Set.BooleanAlgebra
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Order.Basic
public import Mathlib.Order.CompleteBooleanAlgebra
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Support
public import Mathlib.Topology.Basic
public import Mathlib.Topology.Closure
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.LocallyConstant.Basic

@[expose] public section

open Matrix ValuativeRel GlobalTheory.WeilM MeasureTheory
open scoped ComplexConjugate NNReal

namespace GlobalTheory.CompanionTheory.WeilOneMember

section Alg

variable {R : Type} [CommRing R] {E : Type} [CommRing E] [Algebra R E] {c : E →ₐ[R] E}
  {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]



end Alg

theorem boxFun_mem {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] {κ κ' : Type}
    {φ₁ : (κ → R) → ℂ} {φ₂ : (κ' → R) → ℂ} (h₁ : φ₁ ∈ SB (κ → R)) (h₂ : φ₂ ∈ SB (κ' → R)) :
    boxFun φ₁ φ₂ ∈ SB (κ ⊕ κ' → R) := by
  have h₁' : IsLocallyConstant φ₁ ∧ HasCompactSupport φ₁ := h₁
  have h₂' : IsLocallyConstant φ₂ ∧ HasCompactSupport φ₂ := h₂
  have cl : Continuous fun x : κ ⊕ κ' → R => x ∘ Sum.inl := continuous_pi fun i => continuous_apply _
  have cr : Continuous fun x : κ ⊕ κ' → R => x ∘ Sum.inr := continuous_pi fun i => continuous_apply _
  show IsLocallyConstant (boxFun φ₁ φ₂) ∧ HasCompactSupport (boxFun φ₁ φ₂)
  refine ⟨?_, ?_⟩
  · exact IsLocallyConstant.comp₂ (h₁'.1.comp_continuous cl) (h₂'.1.comp_continuous cr) (· * ·)
  · let S : Set (κ ⊕ κ' → R) :=
      (fun x => x ∘ Sum.inl) ⁻¹' tsupport φ₁ ∩ (fun x => x ∘ Sum.inr) ⁻¹' tsupport φ₂
    let gm : (κ → R) × (κ' → R) → (κ ⊕ κ' → R) := fun p => Sum.elim p.1 p.2
    have hgm : Continuous gm := by
      refine continuous_pi fun i => ?_
      cases i with
      | inl i => exact (continuous_apply i).comp continuous_fst
      | inr i => exact (continuous_apply i).comp continuous_snd
    have hK : IsCompact (gm '' (tsupport φ₁ ×ˢ tsupport φ₂)) := (h₁'.2.prod h₂'.2).image hgm
    have hSc : IsClosed S := (isClosed_tsupport φ₁).preimage cl |>.inter ((isClosed_tsupport φ₂).preimage cr)
    have hsub : tsupport (boxFun φ₁ φ₂) ⊆ S := by
      refine closure_minimal ?_ hSc
      intro x hx
      have hx' : φ₁ (x ∘ Sum.inl) * φ₂ (x ∘ Sum.inr) ≠ 0 := hx
      exact ⟨subset_tsupport _ (left_ne_zero_of_mul hx'), subset_tsupport _ (right_ne_zero_of_mul hx')⟩
    have hSK : S ⊆ gm '' (tsupport φ₁ ×ˢ tsupport φ₂) := by
      intro x hx
      exact ⟨(x ∘ Sum.inl, x ∘ Sum.inr), hx, Sum.elim_comp_inl_inr x⟩
    exact hK.of_isClosed_subset (isClosed_tsupport _) (hsub.trans hSK)

end GlobalTheory.CompanionTheory.WeilOneMember
