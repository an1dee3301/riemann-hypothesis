module

public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
public import Init.Core
public import Init.Data.Fin.Basic
public import Init.Data.Nat.Basic
public import Init.Data.NeZero
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Instances
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Logic.Basic
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.GroupCompletion
public import Mathlib.Topology.Algebra.IsUniformGroup.Defs
public import Mathlib.Topology.Algebra.UniformField
public import Mathlib.Topology.Algebra.UniformRing
public import Mathlib.Topology.Algebra.Valued.ValuationTopology
public import Mathlib.Topology.Algebra.Valued.ValuedField
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open Formalism.MainNotions.GL3Theta Formalism.MainNotions.TaylorLogMetric

namespace Formalism.MainNotions.Ext.CutA

def CubeOfTwoIdentities : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : G1 p), g.Ok →
    Simeq (g.phAt (g.add (Xv 0) (Xv 1)) + g.phAt (g.sub (Xv 0) (Xv 1)) : MvPowerSeries (Fin 2) ℂ_[p])
      (2 * g.phAt (Xv 0) + 2 * g.phAt (Xv 1)) →
    Simeq (g.phAt (g.add (g.add (Xv 0) (Xv 1)) (Xv 2)) + g.phAt (g.sub (Xv 0) (Xv 1)) +
        g.phAt (g.sub (Xv 1) (Xv 2)) + g.phAt (g.sub (Xv 2) (Xv 0)) : MvPowerSeries (Fin 3) ℂ_[p])
      (3 * (g.phAt (Xv 0) + g.phAt (Xv 1) + g.phAt (Xv 2))) →
    Simeq (g.phAt (g.add (g.add (Xv 0) (Xv 1)) (Xv 2)) - g.phAt (g.add (Xv 0) (Xv 1)) -
        g.phAt (g.add (Xv 1) (Xv 2)) - g.phAt (g.add (Xv 2) (Xv 0)) +
        g.phAt (Xv 0) + g.phAt (Xv 1) + g.phAt (Xv 2) : MvPowerSeries (Fin 3) ℂ_[p]) 0



def JetsHigh : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : G1 p), g.Ok →
    Simeq (g.phAt (g.add (g.add (Xv 0) (Xv 1)) (Xv 2)) - g.phAt (g.add (Xv 0) (Xv 1)) -
        g.phAt (g.add (Xv 1) (Xv 2)) - g.phAt (g.add (Xv 2) (Xv 0)) +
        g.phAt (Xv 0) + g.phAt (Xv 1) + g.phAt (Xv 2) : MvPowerSeries (Fin 3) ℂ_[p]) 0 →
    ∀ i : ℕ, i ≠ 1 → i ≠ 2 → IsIntP (g.jetPh i)

def JetsOne : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : G1 p), g.Ok → p ≠ 2 →
    Simeq (g.phAt (g.mulBy (-1) (Xv ())) : MvPowerSeries Unit ℂ_[p]) (g.phAt (Xv ())) →
    IsIntP (g.jetPh 1)

def JetsTwo : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : G1 p) (a b : ℂ_[p]), g.Ok →
    Simeq (g.be (g.mulBy a (Xv 0)) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]) (g.be (Xv 0) (g.mulBy b (Xv 1))) →
    IsIntP ((a - b) * g.jetPh 2)

end Formalism.MainNotions.Ext.CutA
