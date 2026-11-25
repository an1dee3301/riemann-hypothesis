module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LagrangianInvariantFormsProportionalFinitePlace
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Prod
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix GlobalTheory.VacAny

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lagrangian_invariant_forms_proportional_finitePlace : ∀ (F : Type) [Field F] [NumberField F] (v : Pl (F := F)) (ψv : AddChar (Fv F v) ℂ), Continuous ψv → ψv ≠ 1 →
    ∀ (κ : Type) [Fintype κ] (Λ : Submodule (Fv F v) ((κ → Fv F v) × (κ → Fv F v))),
    (∀ a ∈ Λ, ∀ b ∈ Λ, a.1 ⬝ᵥ b.2 = b.1 ⬝ᵥ a.2) → Module.finrank (Fv F v) Λ = Fintype.card κ →
    ∀ l₁ l₂ : ((κ → Fv F v) → ℂ) →ₗ[ℂ] ℂ,
    (∀ w ∈ Λ, ∀ φ ∈ SB (κ → Fv F v), l₁ (schr ψv w φ) = l₁ φ) →
    (∀ w ∈ Λ, ∀ φ ∈ SB (κ → Fv F v), l₂ (schr ψv w φ) = l₂ φ) →
    (∃ φ ∈ SB (κ → Fv F v), l₂ φ ≠ 0) → ∃ c : ℂ, ∀ φ ∈ SB (κ → Fv F v), l₁ φ = c * l₂ φ := by
  first | exact @GlobalTheory.LagrInvForm.proportional_at_place | exact GlobalTheory.LagrInvForm.proportional_at_place | (intros; apply GlobalTheory.LagrInvForm.proportional_at_place <;> assumption)
