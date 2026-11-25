module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Core
public import Init.Data.Fin.Basic
public import Init.Data.Fin.Lemmas
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Filter.Cofinite
public import Mathlib.Order.Filter.Defs
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

namespace GlobalTheory.ClosingLemmaThird

theorem main : (let d1 : {F : Type} → [inst : Field F] → [inst_1 : NumberField F] → {κ : Type} → [Fintype κ] → ((v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) → (κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ) → (v₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) → ((κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v₁) → ℂ) → ((κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) → ℂ) → Prop := @(fun {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (vac : (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) → (κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ) (v₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (φ₀ : (κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v₁) → ℂ) (Φ : (κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) → ℂ) ↦ ∃ (m : ℕ) (f : Fin m → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ) (φ : Fin m → (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) → (κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ), Φ = ∑ k : Fin m, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f k) (φ k) ∧ (∀ (k : Fin m) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)), φ k v ∈ GlobalTheory.WeilM.SB (κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)) ∧ (∀ (k : Fin m), ∀ᶠ (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) in Filter.cofinite, φ k v = vac v) ∧ ∀ (k : Fin m), φ k v₁ = φ₀); ∀ {F : Type} [inst : Field F] [inst_1 : NumberField F] {κ : Type} [inst_2 : Fintype κ] {vac : (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) → (κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ} {v₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)} {φ₀ : (κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v₁) → ℂ} {Φ Ψ : (κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) → ℂ}, d1 vac v₁ φ₀ Φ → d1 vac v₁ φ₀ Ψ → d1 vac v₁ φ₀ (Φ + Ψ)) := by
  intro d1 F _ _ κ _ vac v₁ φ₀ Φ Ψ hΦ hΨ
  obtain ⟨m, f, φ, hΦe, h1, h2, h3⟩ := hΦ
  obtain ⟨m', g, ψ, hΨe, g1, g2, g3⟩ := hΨ
  refine ⟨m + m', Fin.append f g, Fin.append φ ψ, ?_, ?_, ?_, ?_⟩
  · rw [hΦe, hΨe, Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
  · intro k v
    refine Fin.addCases (fun i => ?_) (fun i => ?_) k
    · simpa only [Fin.append_left] using h1 i v
    · simpa only [Fin.append_right] using g1 i v
  · intro k
    refine Fin.addCases (fun i => ?_) (fun i => ?_) k
    · simpa only [Fin.append_left] using h2 i
    · simpa only [Fin.append_right] using g2 i
  · intro k
    refine Fin.addCases (fun i => ?_) (fun i => ?_) k
    · simpa only [Fin.append_left] using h3 i
    · simpa only [Fin.append_right] using g3 i

end GlobalTheory.ClosingLemmaThird
