module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicSpectrum.Definitions.MembershipCriteria.GoodChar
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.MembershipProofs.RationalFiniteIdeleFactorization
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.MembershipProofs.Irreducible
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.MembershipProofs.ExistsStdStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.Core20Slim.Development.AutomorphicSpectrum.Definitions.MembershipCriteria.LaEqSqrtSmulLam
public import Init.Core
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Invertible.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.Order.Notation
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Separation.Hausdorff

@[expose] public section

noncomputable section

open GlobalTheory.CompanionTheory.VacLoc GlobalTheory.CompanionTheory.FinHeis GlobalTheory.WeilM MeasureTheory Matrix

namespace GlobalTheory.CompanionTheory.VacLoc.ModelLine

theorem cyclic_and_line : ∀ {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R]
    [T2Space R] [Invertible (2 : R)] (ψ : AddChar R ℂ) (O : Subring R) (u : Rˣ) {W : Type} [AddCommGroup W] [Module R W]
    {B : W → W → R} {κ : Type} [Fintype κ] (d : Darboux B κ) (μ : @Measure (κ → R) (borel _)) (S : Sys W (SB (κ → R)))
    (Γ : AddSubgroup W) (al : W → ℂ) (φ φ' : SB (κ → R)), GoodChar ψ O u → IsModel ψ d μ S →
    (φ ≠ 0 → Cyclic S φ) ∧
      (SelfDual S Γ → IsSemi S al Γ → Law S al Γ φ → Law S al Γ φ' → φ ≠ 0 → ∃ a : ℂ, φ' = a • φ) := by
  intro R _ _ _ _ _ _ ψ O u W _ _ B κ _ d μ S Γ al φ φ' hg hm
  obtain ⟨Γ₀, al₀, φ₀, h1, h2, h3, h4, _⟩ := GlobalTheory.T.schrodinger_model_selfDual_lattice ψ O u d μ S hg hm
  have hcyc : φ ≠ 0 → Cyclic S φ := fun h =>
    (GlobalTheory.CompanionTheory.FinHeis.Irred.irreducible S al₀ Γ₀ φ₀ h1 h2 h3 h4).2 φ h
  refine ⟨hcyc, fun hΓ hal hφ hφ' h0 => ?_⟩
  exact GlobalTheory.CompanionTheory.FinHeis.LawLine.law_line S al Γ φ φ' hΓ hal hφ (hcyc h0) hφ'

end GlobalTheory.CompanionTheory.VacLoc.ModelLine
