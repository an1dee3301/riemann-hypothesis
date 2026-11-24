module

public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.Kleene
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.IsEmpty.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm

@[expose] public section

open Formalism.MainNotions.TaylorLogMetric Formalism.BasicNotions NumberField

namespace Formalism.MainNotions.Ext

section Heis

variable {T I J : Type} [Fintype T] [Fintype I] [Fintype J]

noncomputable def HfG (A : ℝ) (z w : T → I → J → ℂ) : ℂ :=
  (∑ τ, ∑ i, ∑ j, z τ i j * (starRingEnd ℂ) (w τ i j)) / (A : ℂ)

noncomputable def UG (A : ℝ) (x : T → I → J → ℂ) (G : (T → I → J → ℂ) → ℂ) : (T → I → J → ℂ) → ℂ :=
  fun z => G (z + x) * Complex.exp (-(Real.pi : ℂ) * HfG A z x - (Real.pi : ℂ) * HfG A x x / 2)

end Heis

def IdealLattice : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (φ : K →+* ℂ), Module.finrank ℚ K = 2 → IsEmpty (K →+* ℝ) →
    ∀ (cc : Ideal (𝓞 K)) (δ : ℂ), cc ≠ ⊥ → δ ≠ 0 →
      (∃ w₁ w₂ : ℂ, ((starRingEnd ℂ) w₁ * w₂).im ≠ 0 ∧
        AddSubgroup.closure {w | ∃ c ∈ cc, w = δ * φ (c : K)} = AddSubgroup.closure {w₁, w₂}) ∧
      area (AddSubgroup.closure {w | ∃ c ∈ cc, w = δ * φ (c : K)}) =
        ‖δ‖ ^ 2 * (Ideal.absNorm cc : ℝ) * Real.sqrt |(discr K : ℝ)| / 2

end Formalism.MainNotions.Ext
