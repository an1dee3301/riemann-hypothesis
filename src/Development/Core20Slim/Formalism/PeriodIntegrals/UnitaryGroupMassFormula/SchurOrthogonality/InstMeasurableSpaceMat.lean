module

public import Mathlib
public import Development.Core20Slim.Formalism.PeriodIntegrals.SchurFock
public import Formalism.PeriodIntegrals.HwIrred
public import Formalism.LocalRingCardinality.DataCoeff
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.MeasureTheory.OuterMeasure.AE
public import Mathlib.MeasureTheory.OuterMeasure.Defs
public import Mathlib.Order.Filter.Defs
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

namespace PI.WSF

open Formalism.BasicNotions MvPolynomial MeasureTheory

instance instMeasurableSpaceMat (N : ℕ) : MeasurableSpace (Matrix (Fin N) (Fin N) ℂ) := borel _

instance instBorelSpaceMat (N : ℕ) : BorelSpace (Matrix (Fin N) (Fin N) ℂ) := ⟨rfl⟩

def evalM {N : ℕ} (x : Matrix (Fin N) (Fin N) ℂ) (s : MvPolynomial (Fin N × Fin N) ℂ) : ℂ :=
  MvPolynomial.eval (fun v : Fin N × Fin N => x v.1 v.2) s

def EvalOne : Prop :=
  ∀ (N : ℕ) (lam : DomWeight N), ∀ s ∈ nablaSq ℂ N lam, evalM 1 s = normFock lam s (extremal ℂ N lam)

def IsHaarU (N : ℕ) (μ : Measure (Matrix (Fin N) (Fin N) ℂ)) : Prop :=
  IsProbabilityMeasure μ ∧ (∀ᵐ x ∂μ, x ∈ Matrix.unitaryGroup (Fin N) ℂ) ∧
  (∀ u ∈ Matrix.unitaryGroup (Fin N) ℂ, ∀ f : Matrix (Fin N) (Fin N) ℂ → ℂ, Continuous f →
    ∫ x, f (x * u) ∂μ = ∫ x, f x ∂μ) ∧
  (∀ u ∈ Matrix.unitaryGroup (Fin N) ℂ, ∀ f : Matrix (Fin N) (Fin N) ℂ → ℂ, Continuous f →
    ∫ x, f (u * x) ∂μ = ∫ x, f x ∂μ)

def HaarU : Prop := ∀ N : ℕ, ∃ μ : Measure (Matrix (Fin N) (Fin N) ℂ), IsHaarU N μ

def SchurOrth : Prop :=
  ∀ (N : ℕ) (lam : DomWeight N) (μ : Measure (Matrix (Fin N) (Fin N) ℂ)), IsHaarU N μ →
    ∀ s ∈ nablaSq ℂ N lam,
      (normFock lam s s).re = (Module.finrank ℂ (delSq ℂ N lam) : ℝ) * ∫ x, ‖evalM x s‖ ^ 2 ∂μ

end PI.WSF
