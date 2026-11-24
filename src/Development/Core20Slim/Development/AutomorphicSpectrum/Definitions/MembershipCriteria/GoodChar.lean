module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.Core20Slim.Development.AutomorphicSpectrum.Definitions.MembershipCriteria.LaEqSqrtSmulLam
public import Init.Core
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Invertible.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.Order.Filter.Defs
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter

@[expose] public section

noncomputable section

open MeasureTheory Matrix GlobalTheory.WeilM

namespace GlobalTheory.CompanionTheory.VacLoc

section Ground

variable {R : Type} [CommRing R] [TopologicalSpace R]

structure GoodChar (ψ : AddChar R ℂ) (O : Subring R) (u : Rˣ) : Prop where
  norm_one : ∀ x, ‖ψ x‖ = 1
  compact : IsCompact (O : Set R)
  isOpen : IsOpen (O : Set R)
  ann : ∀ x : R, (∀ y ∈ O, ψ (x * y) = 1) ↔ ((u⁻¹ : Rˣ) : R) * x ∈ O
  basis : ∀ U ∈ nhds (0 : R), ∃ v : Rˣ, ∀ y ∈ O, (v : R) * y ∈ U
  den : ∀ x : R, ∃ v : Rˣ, (v : R) ∈ O ∧ (v : R) * x ∈ O

def pair {κ : Type} (μ : @Measure (κ → R) (borel _)) (φ φ' : (κ → R) → ℂ) : ℂ :=
  ∫ x, (starRingEnd ℂ) (φ x) * φ' x ∂μ

variable [Invertible (2 : R)] {W : Type} [AddCommGroup W] [Module R W] {B : W → W → R} {κ : Type} [Fintype κ]

def IsModel (ψ : AddChar R ℂ) (d : Darboux B κ) (μ : @Measure (κ → R) (borel _))
    (S : GlobalTheory.CompanionTheory.FinHeis.Sys W (SB (κ → R))) : Prop :=
  (∀ w (φ : SB (κ → R)), ((S.rho w φ : SB (κ → R)) : (κ → R) → ℂ) = d.rho ψ w φ) ∧
  (∀ φ φ' : SB (κ → R), S.B φ φ' = pair μ φ φ') ∧ ∀ w w', S.c w w' = ψ (⅟(2 : R) * B w w')

end Ground

variable {R : Type} [CommRing R] {E : Type} [CommRing E] [Algebra R E] (c : E →ₐ[R] E)
variable {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

end GlobalTheory.CompanionTheory.VacLoc
