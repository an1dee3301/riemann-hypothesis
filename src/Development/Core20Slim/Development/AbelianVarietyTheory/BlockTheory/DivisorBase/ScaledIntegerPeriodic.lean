module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Support
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Group.Arithmetic
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Fin.Basic
public import Mathlib.Order.Monotone.Defs
public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open MeasureTheory ValuativeRel Matrix
open scoped Pointwise

noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.ScaledIntegerPeriodic
open GlobalTheory.SplitWeil GlobalTheory.SplitWeil.Model GlobalTheory.SplitFlip

section Defs
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def scaledInt (ϖ : kˣ) (a : ℕ) (m : ℤ) : Set (Matrix (Fin a) (Fin a) k) :=
  {Z | ∀ i j, valuation k (Z i j) ≤ valuation k ((ϖ ^ m : kˣ) : k)}


def IsPeriodic (ϖ : kˣ) {a : ℕ} (M : ℤ) (φ : Matrix (Fin a) (Fin a) k → ℂ) : Prop :=
  ∀ X, ∀ Z ∈ scaledInt ϖ a M, φ (X + Z) = φ X

end Defs

def ShellLemma : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (ϖ : kˣ), IsUnif ϖ →
    ∀ (ν : kˣ →* ℂˣ) (e : ℕ), ¬ IsUnram ν → CondLE ϖ e ν →
    ∀ (a : ℕ) (μ : Measure (GL (Fin a) k)) [μ.IsHaarMeasure] (φ : Matrix (Fin a) (Fin a) k → ℂ),
      φ ∈ SB (Matrix (Fin a) (Fin a) k) →
      (∀ (n : Fin a → ℤ) (z : ℂ),
        IntegrableOn (fun g : GL (Fin a) k => φ g.val * (ν (gdet g) : ℂ) * apow (gdet g) z) (shellSet ϖ n) μ) ∧
      (∀ M : ℤ, IsPeriodic ϖ M φ → ∀ n : Fin a → ℤ, (∃ i, M ≤ n i) → ∀ z : ℂ, shell μ ϖ ν z φ n = 0) ∧
      (∀ M' : ℕ, Function.support φ ⊆ scaledInt ϖ a (-(M' : ℤ)) →
        ∀ n : Fin a → ℤ, ¬ (∀ i, -(M' : ℤ) ≤ n i) → ∀ z : ℂ, shell μ ϖ ν z φ n = 0) ∧
      {n : {n : Fin a → ℤ // Antitone n} | ∃ z : ℂ, shell μ ϖ ν z φ n.1 ≠ 0}.Finite

end GlobalTheory.IndefiniteRowSideFullHecke.ScaledIntegerPeriodic
