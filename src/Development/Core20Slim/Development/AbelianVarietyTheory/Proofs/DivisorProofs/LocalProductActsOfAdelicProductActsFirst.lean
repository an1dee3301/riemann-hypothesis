module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagWZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplementaryAdelicSchwartzRestFunction
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductFunctionOnSumCoordsMemAdelicSchwartzSpace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels MeasureTheory GlobalTheory.LatVac GlobalTheory.InertVacLag GlobalTheory.InertLagChar
open scoped TensorProduct Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BoxAct

theorem tens_boxFun {F : Type} [Field F] [NumberField F] {R κ κ' : Type} (ev : AF F → R)
    (φ₁ : (κ → R) → ℂ) (φ₂ : (κ' → R) → ℂ) (r₁ : (κ → AF F) → ℂ) (r₂ : (κ' → AF F) → ℂ) :
    tens ev (boxFun φ₁ φ₂) (boxFun r₁ r₂) = boxFun (tens ev φ₁ r₁) (tens ev φ₂ r₂) := by
  funext x
  simp only [tens, boxFun, Function.comp_def]
  ring

theorem boxFun_acts : ∀ (F : Type) [Field F] [NumberField F] (v : Pl (F := F)) (κ κ' : Type) [Fintype κ] [Fintype κ']
    (T : ((κ → AF F) → ℂ) → (κ → AF F) → ℂ) (Td : ((κ ⊕ κ' → AF F) → ℂ) → (κ ⊕ κ' → AF F) → ℂ),
    (∀ Φ₁ ∈ schA F κ, ∀ Φ₂ ∈ schA F κ', Td (boxFun Φ₁ Φ₂) = boxFun (T Φ₁) Φ₂) →
    ∀ φ₁ ∈ SB (κ → Fv F v), ∀ φ₂ ∈ SB (κ' → Fv F v), ∀ (φ₁' : (κ → Fv F v) → ℂ) (Φ' : (κ ⊕ κ' → Fv F v) → ℂ),
      Acts (evFin F v) T φ₁ φ₁' → Acts (evFin F v) Td (boxFun φ₁ φ₂) Φ' → Φ' = boxFun φ₁' φ₂ := by
  intro F _ _ v κ κ' _ _ T Td hT φ₁ hφ₁ φ₂ hφ₂ φ₁' Φ' h₁ hd
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.RestWitness.exists_rest κ v
  obtain ⟨R', hR0', hR'⟩ := GlobalTheory.RestWitness.exists_rest κ' v
  have r₁ := hR φ₁ hφ₁
  have r₂ := hR' φ₂ hφ₂
  have hRest : Rest (evFin F v) (boxFun φ₁ φ₂) (boxFun R R') := by
    refine ⟨fun x z hz => ?_, ?_⟩
    · have hz₁ : At (evFin F v) (z ∘ Sum.inl) := fun u hu => by
        funext i; exact congrFun (hz u hu) (Sum.inl i)
      have hz₂ : At (evFin F v) (z ∘ Sum.inr) := fun u hu => by
        funext i; exact congrFun (hz u hu) (Sum.inr i)
      have e₁ := r₁.1 (x ∘ Sum.inl) (z ∘ Sum.inl) hz₁
      have e₂ := r₂.1 (x ∘ Sum.inr) (z ∘ Sum.inr) hz₂
      simp only [boxFun]
      have a₁ : (x + z) ∘ Sum.inl = x ∘ Sum.inl + z ∘ Sum.inl := rfl
      have a₂ : (x + z) ∘ Sum.inr = x ∘ Sum.inr + z ∘ Sum.inr := rfl
      rw [a₁, a₂, e₁, e₂]
    · rw [tens_boxFun]
      exact GlobalTheory.SchwartzBox.boxFun_mem_schA F κ κ' _ r₁.2 _ r₂.2
  have key : tens (evFin F v) Φ' (boxFun R R') = tens (evFin F v) (boxFun φ₁' φ₂) (boxFun R R') := by
    rw [← hd _ hRest, tens_boxFun, hT _ r₁.2 _ r₂.2, h₁ R r₁, tens_boxFun]
  funext y
  let z : κ ⊕ κ' → AF F := fun i => GlobalTheory.LatVac.liftV v (y i)
  have hz : ∀ (ι : Type) (w : ι → κ ⊕ κ'), At (evFin F v) (z ∘ w) := by
    intro ι w u hu
    funext i
    exact GlobalTheory.LatVac.at_liftV v (y (w i)) u hu
  have hRz : boxFun R R' z = R 0 * R' 0 := by
    have e₁ := (hR φ₁ hφ₁).1 0 (z ∘ Sum.inl) (hz κ Sum.inl)
    have e₂ := (hR' φ₂ hφ₂).1 0 (z ∘ Sum.inr) (hz κ' Sum.inr)
    rw [zero_add] at e₁ e₂
    simp only [boxFun]
    rw [e₁, e₂]
  have hev : (fun i => evFin F v (z i)) = y := by
    funext i; exact GlobalTheory.LatVac.evFin_liftV v (y i)
  have e := congrFun key z
  simp only [tens, hev, hRz] at e
  exact mul_right_cancel₀ (mul_ne_zero hR0 hR0') e

end GlobalTheory.BoxAct
