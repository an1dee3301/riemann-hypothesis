module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CosetSumAlongMulEquivSubgroups
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.LatticeFrames.HalfData
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
public import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
public import Development.AbelianVarietyTheory.Definitions.Foundations.AnalyticOnNhdTsumNpow
public import Init.Core
public import Init.Prelude
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic

@[expose] public section

open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cosetSum_along_mulEquiv_subgroups : ∀ (G₁ G₂ : Type) [Group G₁] [Group G₂] (κ : G₁ ≃* G₂) (P₁ Γ₁ : Subgroup G₁) (P₂ Γ₂ : Subgroup G₂), (∀ g, g ∈ P₁ ↔ κ g ∈ P₂) → (∀ g, g ∈ Γ₁ ↔ κ g ∈ Γ₂) → ∀ (Φ₂ : G₂ → ℂ) (x : G₁) (c : ℂ) (Φ₁ : G₁ → ℂ), (∀ g, Φ₁ g = c * Φ₂ (κ (g * x))) → LeftInv (P₂ ⊓ Γ₂) Φ₂ → LeftInv (P₁ ⊓ Γ₁) Φ₁ ∧ ∀ g, (GlobalTheory.Eis.CosetConv P₂ Γ₂ Φ₂ (κ (g * x)) → GlobalTheory.Eis.CosetConv P₁ Γ₁ Φ₁ g) ∧ GlobalTheory.Eis.cosetSum P₁ Γ₁ Φ₁ g = c * GlobalTheory.Eis.cosetSum P₂ Γ₂ Φ₂ (κ (g * x)) := by
  first | exact @GlobalTheory.StdUnn.cosetSum_along_mulEquiv | exact GlobalTheory.StdUnn.cosetSum_along_mulEquiv | (intros; apply GlobalTheory.StdUnn.cosetSum_along_mulEquiv <;> assumption)
