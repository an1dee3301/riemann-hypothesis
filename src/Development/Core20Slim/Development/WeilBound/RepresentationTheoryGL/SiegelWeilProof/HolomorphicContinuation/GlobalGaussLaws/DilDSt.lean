module

public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.IteratedDerivOfReal
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocOpSt
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SProd
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

open Topology

namespace PositivityTheory.Rg.Sw.Glob

def ContDeriv : Prop :=
  ∀ (m n : ℕ) (U : Set ℂ), IsOpen U → ∀ f : ℂ → (Fin m → Fin n → ℂ) → ℂ,
    ContinuousOn (fun p : ℂ × (Fin m → Fin n → ℂ) => f p.1 p.2) (U ×ˢ Set.univ) →
    (∀ u, DifferentiableOn ℂ (fun z => f z u) U) →
    ∀ r : ℕ, ContinuousOn (fun p : ℂ × (Fin m → Fin n → ℂ) => iteratedDeriv r (fun z => f z p.2) p.1) (U ×ˢ Set.univ)

def SchScale : Prop :=
  ∀ (m n : ℕ) (f : (Fin m → Fin n → ℂ) → ℂ) (s : ℝ) (X : Fin n → ℝ) (a : ℂ), IsSch f →
    IsSch (fun u => a * f (fun i j => u i j * Real.exp (s * X j)))

end PositivityTheory.Rg.Sw.Glob
