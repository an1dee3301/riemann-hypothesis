module

public import Mathlib
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.SingToDiffAlt
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.IsSingTest
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.WithTop
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.ENat.Basic
public import Mathlib.Data.ENat.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Matrix.Basis
public import Mathlib.Data.Matrix.Block
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.Order.Notation
public import Mathlib.Order.TypeTags
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

open MeasureTheory Matrix
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.LVs.II

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def reK (e : M2 n) : M2 n := (1 / 2 : ℂ) • (e - eᴴ)

def imK (e : M2 n) : M2 n := (-Complex.I / 2) • (e + eᴴ)

def dK (F : M2 n → ℂ) (x e : M2 n) : ℂ := fderiv ℝ F x (reK e * x) + Complex.I * fderiv ℝ F x (imK e * x)

def KSet (n : ℕ) : Set (M2 n) := {g | InK g}

def LeftDeriv : Prop :=
  ∀ (n : ℕ) (Kg : Type) [Group Kg] [TopologicalSpace Kg] [IsTopologicalGroup Kg] [CompactSpace Kg] [MeasurableSpace Kg]
    [BorelSpace Kg] (μ : Measure Kg) [μ.IsHaarMeasure] (ι : Kg →* M2 n), Continuous ι → (∀ g, InK g ↔ ∃ k, ι k = g) →
    ∀ (F : M2 n → ℂ) (U : Set (M2 n)), IsOpen U → KSet n ⊆ U → ContDiffOn ℝ 1 F U →
    ∀ e : M2 n, e * JJ n = JJ n * e →
      Integrable (fun k => dK F (ι k) e) μ ∧ ∫ k, dK F (ι k) e ∂μ = 0

def LawDeriv : Prop :=
  ∀ (n : ℕ) (Θ : M2 n → ℂ) (Ω : Set (M2 n)), IsOpen Ω → {g | InG g} ⊆ Ω → DifferentiableOn ℂ Θ Ω →
    (∀ p x, InG p → p.toBlocks₂₁ = 0 → InG x → Θ (p * x) = ((‖(p.toBlocks₂₂).det‖ ^ (-(2 * (n : ℤ))) : ℝ) : ℂ) * Θ x) →
    ∀ x, InG x → ∀ Y : M2 n, Y.toBlocks₂₁ = 0 →
      fderiv ℂ Θ x (Y * x) = (n : ℂ) * (Y.toBlocks₁₁.trace - Y.toBlocks₂₂.trace) * Θ x

def eA (a b : Fin n) : M2 n := fromBlocks (Matrix.single a b 1) 0 0 (Matrix.single a b 1)

def eB (a b : Fin n) : M2 n := fromBlocks 0 (Matrix.single a b 1) (-Matrix.single a b 1) 0

def cA (Z : M2 n) (a b : Fin n) (x : M2 n) : ℂ := (x * Z * xᴴ).toBlocks₂₂ a b

def cB (Z : M2 n) (a b : Fin n) (x : M2 n) : ℂ := -(x * Z * xᴴ).toBlocks₂₁ a b

def PtId : Prop :=
  ∀ (n : ℕ) (Θ : M2 n → ℂ) (x Z : M2 n), InK x → ContDiffAt ℂ 1 Θ x →
    (∀ Y : M2 n, Y.toBlocks₂₁ = 0 → fderiv ℂ Θ x (Y * x) = (n : ℂ) * (Y.toBlocks₁₁.trace - Y.toBlocks₂₂.trace) * Θ x) →
    fderiv ℂ Θ x (x * Z) =
      ∑ a, ∑ b, (dK (fun y => cA Z a b y * Θ y) x (eA a b) + dK (fun y => cB Z a b y * Θ y) x (eB a b))

def CDiff : Prop := ∀ (n : ℕ) (Z : M2 n) (a b : Fin n), ContDiff ℝ ∞ (cA Z a b) ∧ ContDiff ℝ ∞ (cB Z a b)

end PositivityTheory.Rg.Sw.LVs.II
