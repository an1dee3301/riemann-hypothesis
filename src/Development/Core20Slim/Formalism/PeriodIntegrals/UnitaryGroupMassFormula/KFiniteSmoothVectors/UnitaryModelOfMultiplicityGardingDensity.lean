module

public import Mathlib
public import Formalism.PeriodIntegrals.UpqRep
public import Formalism.PeriodIntegrals.KFinSmooth
public import Init.Core
public import Init.Data.Nat.Basic
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.ENat.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Order.Notation
public import Mathlib.Order.TypeTags
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Algebra.Support
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Cauchy
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open MeasureTheory Matrix Topology
open scoped InnerProductSpace ContDiff

noncomputable section

namespace PI.KFinSmoothW

open PI.UpqRep

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section Defs

variable {n : ℕ} (ε : Fin n → Bool) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def gv (τ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (Φ : Matrix (Fin n) (Fin n) ℂ → ℂ) (x : H) : H :=
  ∫ h, Φ (umat h) • τ (umat h) x ∂(muG ε)

def SmoothJ (τ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (y : H) : Prop :=
  SmoothOnH (Jm ε) (fun g => τ g y)

end Defs

def StepGarding : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (τ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsURepOn (UJset ε) τ →
    ∀ Φ : Matrix (Fin n) (Fin n) ℂ → ℂ, ContDiff ℝ ∞ Φ → HasCompactSupport Φ →
      ∀ x : H, SmoothJ ε τ (gv ε τ Φ x)

def StepDenseW : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (τ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsURepOn (UJset ε) τ →
    ∀ W : Submodule ℂ H, FiniteDimensional ℂ W →
      ∃ Φ : Matrix (Fin n) (Fin n) ℂ → ℂ, ContDiff ℝ ∞ Φ ∧ HasCompactSupport Φ ∧
        (∀ a ∈ Kset ε, ∀ m, Φ (a * m * aᴴ) = Φ m) ∧
        ∀ w ∈ W, ‖gv ε τ Φ w - w‖ ≤ ‖w‖ / 2

end PI.KFinSmoothW
