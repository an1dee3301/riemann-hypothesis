module

public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
public import Init.Core
public import Init.Data.Fin.Basic
public import Init.Data.Nat.Basic
public import Init.Data.NeZero
public import Init.Data.Prod
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Instances
public import Mathlib.Analysis.Normed.Group.Completion
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Logic.Basic
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.GroupCompletion
public import Mathlib.Topology.Algebra.IsUniformGroup.Defs
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.UniformField
public import Mathlib.Topology.Algebra.UniformRing
public import Mathlib.Topology.Algebra.Valued.ValuationTopology
public import Mathlib.Topology.Algebra.Valued.ValuedField
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Completion
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open Formalism.MainNotions.GL3Theta Formalism.MainNotions.TaylorLogMetric

namespace Formalism.MainNotions.Ext.CutA

def PhNormClosed : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : G1 p) (T : Set (ℂ_[p] × ℂ_[p])), g.Ok →
    (∀ α ∈ T, IntegralMv (g.mulBy α.1 (Xv ()) : MvPowerSeries Unit ℂ_[p])) →
    (∀ α ∈ T, Simeq (g.phAt (g.mulBy α.1 (Xv ())) : MvPowerSeries Unit ℂ_[p])
        (MvPowerSeries.C (α.1 * α.2) * g.phAt (Xv ()))) →
    ∀ α ∈ closure T, Simeq (g.phAt (g.mulBy α.1 (Xv ())) : MvPowerSeries Unit ℂ_[p])
        (MvPowerSeries.C (α.1 * α.2) * g.phAt (Xv ()))

def PhNormOfUnits : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : G1 p) (S : Set (ℂ_[p] × ℂ_[p])), g.Ok → p ≠ 2 →
    ((2 : ℂ_[p]), (2 : ℂ_[p])) ∈ S → (∀ α ∈ S, α.swap ∈ S) → (∀ α ∈ S, ∀ β ∈ S, α + β ∈ S) →
    (∀ α ∈ S, ∀ β ∈ S, α * β ∈ S) →
    (∀ α ∈ S, IntegralMv (g.mulBy α.1 (Xv ()) : MvPowerSeries Unit ℂ_[p])) →
    IntegralMv (g.add (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]) →
    (∀ α ∈ S, ∃ n : ℤ_[p], α.1 + α.2 = zc n) → (∀ α ∈ S, ∃ n : ℤ_[p], α.1 * α.2 = zc n) →
    (∀ α ∈ S, ∃ β ∈ S, ∃ γ ∈ S, ‖β.1‖ = 1 ∧ ‖β.2‖ = 1 ∧ ‖γ.1‖ = 1 ∧ ‖γ.2‖ = 1 ∧ α = β + γ) →
    Simeq (g.be (g.add (Xv 0) (Xv 1)) (Xv 2) : MvPowerSeries (Fin 3) ℂ_[p])
      (g.be (Xv 0) (Xv 2) + g.be (Xv 1) (Xv 2)) →
    (∀ α ∈ S, ‖α.1‖ = 1 → ‖α.2‖ = 1 → Simeq (g.phAt (g.mulBy α.1 (Xv ())) : MvPowerSeries Unit ℂ_[p])
        (MvPowerSeries.C (α.1 * α.2) * g.phAt (Xv ()))) →
    ∀ α ∈ S, Simeq (g.phAt (g.mulBy α.1 (Xv ())) : MvPowerSeries Unit ℂ_[p])
        (MvPowerSeries.C (α.1 * α.2) * g.phAt (Xv ()))

end Formalism.MainNotions.Ext.CutA
