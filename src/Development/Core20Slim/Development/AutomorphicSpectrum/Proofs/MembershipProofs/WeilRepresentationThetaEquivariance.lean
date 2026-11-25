module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.MembershipProofs.ThetaSumAdmissibilityStatement
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.MembershipProofs.HeisenbergCommutingOperatorScalarStatement
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.MembershipProofs.ThetaDistributionNonzeroAdmissibleStatement
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.MembershipProofs.AdelicCharacterRationalDualStatement
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Invertible.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.SummationFilter
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open Matrix NumberField IsDedekindDomain GlobalTheory.WeilM MeasureTheory
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.AdelicSchur

theorem schur : ∀ (F : Type) [Field F] [NumberField F] [LocallyCompactSpace (AdeleRing (𝓞 F) F)] [Invertible (2 : AdeleRing (𝓞 F) F)] (κ : Type) [Fintype κ] (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ), Continuous ψ → ψ ≠ 1 → (∀ a : F, ψ (algebraMap F (AdeleRing (𝓞 F) F) a) = 1) → ∀ T : Module.End ℂ ((κ → AdeleRing (𝓞 F) F) → ℂ), (∀ Φ ∈ schA F κ, T Φ ∈ schA F κ) → (∀ l ∈ (adeleClass F).adm κ, l ∘ₗ T ∈ (adeleClass F).adm κ) → (∀ w, ∀ Φ ∈ schA F κ, T (schr ψ w Φ) = schr ψ w (T Φ)) → ∃ a : ℂ, ∀ Φ ∈ schA F κ, T Φ = a • Φ := by
  intro F _ _ _ _ κ _ ψ hψc hψ1 hψF T hTS hTadm hTcomm
  obtain ⟨-, ⟨l₀, hl₀adm, hl₀⟩, -⟩ :=
    GlobalTheory.T.theta_distribution_nonzero_admissible F κ
  obtain ⟨hρS, hθinv⟩ :=
    GlobalTheory.T.theta_distribution_heisenberg_invariant F κ ψ hψc hψ1 hψF
  obtain ⟨a, ha⟩ := GlobalTheory.T.admissible_functional_rational_invariance F κ ψ hψc hψ1 hψF
    (l₀ ∘ₗ T) (hTadm l₀ hl₀adm) (by
      intro w Φ hΦ
      rw [LinearMap.comp_apply, LinearMap.comp_apply, hTcomm _ Φ hΦ,
        hl₀ _ (hρS _ _ (hTS Φ hΦ)), hl₀ _ (hTS Φ hΦ)]
      exact hθinv w (T Φ))
  have ha' : ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, l₀ (T Φ) = a * _ := ha
  refine ⟨a, fun Φ hΦ => ?_⟩
  have hlin : ∀ w, GlobalTheory.WeilM.schr ψ w (T Φ - a • Φ) =
      GlobalTheory.WeilM.schr ψ w (T Φ) - a • GlobalTheory.WeilM.schr ψ w Φ := by
    intro w
    funext x
    simp only [GlobalTheory.WeilM.schr, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hmem : T Φ - a • Φ ∈ GlobalTheory.WeilM.schA F κ :=
    Submodule.sub_mem _ (hTS Φ hΦ) (Submodule.smul_mem _ a hΦ)
  refine sub_eq_zero.mp (GlobalTheory.T.theta_heisenberg_translates_separate F κ ψ hψc hψ1
    hψF _ hmem fun w => ?_)
  rw [← hl₀ _ (hρS w _ hmem), hlin w, map_sub, map_smul, ← hTcomm w Φ hΦ,
    ha' _ (hρS w Φ hΦ), hl₀ _ (hρS w Φ hΦ), smul_eq_mul, sub_self]

end GlobalTheory.CompanionTheory.AdelicSchur
