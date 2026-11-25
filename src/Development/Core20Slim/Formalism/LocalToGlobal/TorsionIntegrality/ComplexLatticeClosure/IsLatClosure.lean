module

public import Development.Core20Slim.Formalism.LocalToGlobal.TorsionIntegrality.ComplexLatticeClosure.ExistsTwoTorsionOffKernels
public import Development.Core20Slim.Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.PeriodRelations.ConjCls
public import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.EpsteinZeta.DedekindFactorK
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.GroupWithZero.Subgroup
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Logic.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.Ideal.Defs

@[expose] public section

noncomputable section

namespace Formalism.L2.Th1.F2

open NumberField
open scoped Pointwise
open Formalism.BasicNotions (D7)
open Formalism.L2.GlobalTheoryTheory Formalism.MainNotions
open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5 (latI UniqInv CMConjSet)

def IsLatClosure : Prop :=
  ∀ a b : ℂ, ((starRingEnd ℂ) a * b).im ≠ 0 → IsLat (AddSubgroup.closure {a, b})

def IsLatSmul : Prop := ∀ (Λ : AddSubgroup ℂ) (c : ℂ), c ≠ 0 → IsLat Λ → IsLat (c • Λ)

def LatILat : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) [Fact d.Prime], d % 4 = 3 → ∀ x : K, x ^ 2 = -(d : K) →
    Module.finrank ℚ K = 2 → ∀ (φ : K →+* ℂ) (𝔞 : Ideal (𝓞 K)) (δ : ℂ), 𝔞 ≠ ⊥ → δ ≠ 0 →
      IsLat (latI φ 𝔞 δ) ∧ HasCM d (latI φ 𝔞 δ)

end Formalism.L2.Th1.F2
