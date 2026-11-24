module

public import Mathlib
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.VacOut
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.DSlope
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SProd
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Set.CoeSort
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Topology.Algebra.ConstMulAction
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.CompactOpen
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.ContinuousMap.Algebra
public import Mathlib.Topology.ContinuousMap.Defs
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology

namespace PositivityTheory.Rg.Sw.AbsSt

def BanachHol : Prop := ∀ (X : Type) [TopologicalSpace X] [CompactSpace X] (U : Set ℂ) (F : ℂ → X → ℂ), IsOpen U →
  ContinuousOn (fun y : ℂ × X => F y.1 y.2) (U ×ˢ univ) → (∀ x, DifferentiableOn ℂ (fun z => F z x) U) →
  ∃ Φ : ℂ → C(X, ℂ), DifferentiableOn ℂ Φ U ∧ ∀ z ∈ U, ∀ x, Φ z x = F z x

def DslopeFam : Prop := ∀ (X : Type) [TopologicalSpace X] [LocallyCompactSpace X] (U : Set ℂ) (s₀ : ℂ) (F : ℂ → X → ℂ),
  IsOpen U → s₀ ∈ U → ContinuousOn (fun y : ℂ × X => F y.1 y.2) (U ×ˢ univ) → (∀ x, DifferentiableOn ℂ (fun z => F z x) U) →
  (∀ x, F s₀ x = 0) →
  ContinuousOn (fun y : ℂ × X => dslope (fun z => F z y.2) s₀ y.1) (U ×ˢ univ) ∧
    ∀ x, DifferentiableOn ℂ (fun z => dslope (fun z => F z x) s₀ z) U

def FactorL : Prop := ∀ (G : Type) [TopologicalSpace G] (S : Submodule ℂ (G → ℂ)) (l : (G → ℂ) → ℂ) (C : Set G),
  IsCompact C → (∀ F ∈ S, Continuous F) → (∀ (a : ℂ), ∀ F ∈ S, ∀ F' ∈ S, l (a • F + F') = a * l F + l F') →
  (∀ F ∈ S, ∀ M : ℝ, (∀ x ∈ C, ‖F x‖ ≤ M) → ‖l F‖ ≤ M) →
  ∃ L : C(C, ℂ) →L[ℂ] ℂ, ∀ F ∈ S, ∀ (hF : Continuous F), l F = L ⟨fun x => F x, hF.comp continuous_subtype_val⟩


end PositivityTheory.Rg.Sw.AbsSt
