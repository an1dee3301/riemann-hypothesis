module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagWZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerIrreducibleFinitePlaceCompletion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerMemSchwartzBruhatFinitePlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIntegralPointsIndicatorIsVacuum
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Core
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Invertible.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Invertible
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Ker
public import Mathlib.Algebra.Module.Submodule.Map
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Notation.Indicator
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Logic.Basic
public import Mathlib.Basic.SProd
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Support
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Separation.Basic
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels MeasureTheory GlobalTheory.LatVac GlobalTheory.InertVacLag GlobalTheory.InertLagChar
open scoped TensorProduct Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BoxSpan

theorem boxFun_mem_SB' {k : Type} [CommRing k] [TopologicalSpace k] [T2Space k] {κ κ' : Type}
    {φ₁ : (κ → k) → ℂ} {φ₂ : (κ' → k) → ℂ} (h₁ : φ₁ ∈ SB (κ → k)) (h₂ : φ₂ ∈ SB (κ' → k)) :
    boxFun φ₁ φ₂ ∈ SB (κ ⊕ κ' → k) := by
  have cl : Continuous fun x : κ ⊕ κ' → k => x ∘ Sum.inl := continuous_pi fun i => continuous_apply _
  have cr : Continuous fun x : κ ⊕ κ' → k => x ∘ Sum.inr := continuous_pi fun i => continuous_apply _
  refine ⟨(h₁.1.comp_continuous cl).mul (h₂.1.comp_continuous cr), ?_⟩
  let e := (Homeomorph.sumArrowHomeomorphProdArrow (X := k) (ι := κ) (ι' := κ'))
  refine HasCompactSupport.intro ((h₁.2.prod h₂.2).image e.symm.continuous) fun x hx => ?_
  have hx' : e x ∉ tsupport φ₁ ×ˢ tsupport φ₂ := fun h => hx ⟨e x, h, e.symm_apply_apply x⟩
  rw [Homeomorph.sumArrowHomeomorphProdArrow_apply, Set.mem_prod, not_and_or] at hx'
  simp only [boxFun]
  rcases hx' with h | h
  · rw [image_eq_zero_of_notMem_tsupport h, zero_mul]
  · rw [image_eq_zero_of_notMem_tsupport h, mul_zero]

theorem schr_boxFun {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) {κ κ' : Type} [Fintype κ]
    [Fintype κ'] (w : (κ ⊕ κ' → R) × (κ ⊕ κ' → R)) (φ₁ : (κ → R) → ℂ) (φ₂ : (κ' → R) → ℂ) :
    schr ψ w (boxFun φ₁ φ₂) = boxFun (schr ψ (w.1 ∘ Sum.inl, w.2 ∘ Sum.inl) φ₁)
      (schr ψ (w.1 ∘ Sum.inr, w.2 ∘ Sum.inr) φ₂) := by
  funext x
  simp only [schr, boxFun, dotProduct, Fintype.sum_sum_type, Function.comp_apply, Pi.add_apply]
  rw [show (∑ i, x (Sum.inl i) * w.2 (Sum.inl i)) + (∑ i, x (Sum.inr i) * w.2 (Sum.inr i)) +
      ⅟(2 : R) * ((∑ i, w.1 (Sum.inl i) * w.2 (Sum.inl i)) + (∑ i, w.1 (Sum.inr i) * w.2 (Sum.inr i))) =
      ((∑ i, x (Sum.inl i) * w.2 (Sum.inl i)) + ⅟(2 : R) * (∑ i, w.1 (Sum.inl i) * w.2 (Sum.inl i))) +
      ((∑ i, x (Sum.inr i) * w.2 (Sum.inr i)) + ⅟(2 : R) * (∑ i, w.1 (Sum.inr i) * w.2 (Sum.inr i))) by ring,
    AddChar.map_add_eq_mul]
  rw [show (x + w.1) ∘ Sum.inl = x ∘ Sum.inl + w.1 ∘ Sum.inl from rfl,
    show (x + w.1) ∘ Sum.inr = x ∘ Sum.inr + w.1 ∘ Sum.inr from rfl]
  ring

end GlobalTheory.BoxSpan


open GlobalTheory.BoxSpan in
theorem GlobalTheory.BoxSpan.boxSpan_ker : ∀ (F : Type) [Field F] [NumberField F] (v : Pl (F := F)) (κ κ' : Type) [Fintype κ] [Fintype κ'] (ψ : AddChar (Fv F v) ℂ), Continuous ψ → ψ ≠ 1 →
    ∀ Λ : ((κ ⊕ κ' → Fv F v) → ℂ) →ₗ[ℂ] ℂ,
      (∀ φ₁ ∈ SB (κ → Fv F v), ∀ φ₂ ∈ SB (κ' → Fv F v), Λ (boxFun φ₁ φ₂) = 0) → ∀ Φ ∈ SB (κ ⊕ κ' → Fv F v), Λ Φ = 0 := by
  intro F _ _ v κ κ' _ _ ψ hψ h1 Λ hΛ Φ hΦ
  classical
  let N : Submodule ℂ ((κ ⊕ κ' → Fv F v) → ℂ) := Submodule.span ℂ
    {f | ∃ φ₁ ∈ SB (κ → Fv F v), ∃ φ₂ ∈ SB (κ' → Fv F v), f = boxFun φ₁ φ₂}
  have hN : N ≤ SB (κ ⊕ κ' → Fv F v) := by
    refine Submodule.span_le.2 ?_
    rintro f ⟨φ₁, h₁, φ₂, h₂, rfl⟩
    exact boxFun_mem_SB' h₁ h₂
  have hS : ∀ w, ∀ φ ∈ N, schr ψ w φ ∈ N := by
    intro w
    let Lw : ((κ ⊕ κ' → Fv F v) → ℂ) →ₗ[ℂ] ((κ ⊕ κ' → Fv F v) → ℂ) :=
      { toFun := schr ψ w
        map_add' := fun f g => by funext x; simp [schr, mul_add]
        map_smul' := fun c f => by funext x; simp [schr]; ring }
    have : N ≤ N.comap Lw := by
      refine Submodule.span_le.2 ?_
      rintro f ⟨φ₁, h₁, φ₂, h₂, rfl⟩
      show schr ψ w (boxFun φ₁ φ₂) ∈ N
      rw [schr_boxFun]
      exact Submodule.subset_span ⟨_, GlobalTheory.SchrSBFin.schr_mem_SB v ψ hψ _ _ h₁, _,
        GlobalTheory.SchrSBFin.schr_mem_SB v ψ hψ _ _ h₂, rfl⟩
    exact fun φ hφ => this hφ
  let i₁ := Set.indicator {x : κ → Fv F v | ∀ k, x k ∈ v.adicCompletionIntegers F} (1 : (κ → Fv F v) → ℂ)
  let i₂ := Set.indicator {x : κ' → Fv F v | ∀ k, x k ∈ v.adicCompletionIntegers F} (1 : (κ' → Fv F v) → ℂ)
  have h0 : boxFun i₁ i₂ ∈ N := Submodule.subset_span
    ⟨i₁, GlobalTheory.StdVacuum.indicator_mem_SB v, i₂, GlobalTheory.StdVacuum.indicator_mem_SB v, rfl⟩
  have hne : boxFun i₁ i₂ ≠ 0 := by
    intro h
    have := congrFun h 0
    simp [boxFun, i₁, i₂, Set.indicator, zero_mem] at this
  have hall := GlobalTheory.SchrIrred.schr_irreducible v ψ hψ h1 N hN hS _ h0 hne
  have hk : N ≤ LinearMap.ker Λ := by
    refine Submodule.span_le.2 ?_
    rintro f ⟨φ₁, h₁, φ₂, h₂, rfl⟩
    exact hΛ φ₁ h₁ φ₂ h₂
  rw [← hall] at hΦ
  exact hk hΦ
