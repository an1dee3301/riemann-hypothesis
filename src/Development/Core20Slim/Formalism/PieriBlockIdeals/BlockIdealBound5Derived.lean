module

public import Mathlib
public import Formalism.SatakeDualWeyl.Statement
public import Development.Core20Slim.Formalism.RankGapBounds.TheoremALocOfLemmaA
public import Development.Core20Slim.Formalism.PieriBlockIdeals.Statement
public import Development.Core20Slim.Formalism.PieriBlockIdeals.FactorialValuationSum
public import Development.Core20Slim.Formalism.PieriBlockIdeals.StatementLA

@[expose] public section

noncomputable section

open TensorProduct MvPolynomial CategoryTheory CategoryTheory.Limits

namespace Formalism.CohomologicalDescent.DepthNonnegative

open Formalism.UG Formalism.RankGapBounds.FormsTensorLocalization Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.LD Formalism.CohomologicalDescent.UnitNormBounds












def repOf (O : Type) [CommRing O] {A : Type} [Ring A] [Algebra O A] {G : Type} [Group G]
    {K : Subgroup G} (jK : K →* A) (W : Type) [AddCommGroup W] [Module O W] [Module A W]
    [IsScalarTower O A W] : Representation O K W :=
  ((Algebra.lsmul O O W : A →ₐ[O] Module.End O W) : A →* Module.End O W).comp jK

abbrev Forms (O : Type) [CommRing O] {A : Type} [Ring A] [Algebra O A] {G : Type} [Group G]
    (Γ : Subgroup G) {K : Subgroup G} (jK : K →* A) (W : Type) [AddCommGroup W] [Module O W]
    [Module A W] [IsScalarTower O A W] : Submodule O (G → W) :=
  AMFK O Γ K (repOf O jK W)







abbrev NablaT (O : Type) [CommRing O] (N : ℕ) {ι : Type} (lam : ι → ℕ → ℕ) : Type :=
  ⨂[O] τ : ι, dualWeyl O N N (res N (lam τ))

















end Formalism.CohomologicalDescent.DepthNonnegative
