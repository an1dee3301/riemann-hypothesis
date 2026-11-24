module

public import Development.Core20Slim.Formalism.SharpRestriction.GlobalSchurBounds.StatementTranslationInvariantSeventh
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
public import Mathlib.Topology.Algebra.UniformField
public import Mathlib.Topology.Algebra.UniformRing
public import Mathlib.Topology.Algebra.Valued.ValuationTopology
public import Mathlib.Topology.Algebra.Valued.ValuedField
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open Formalism.MainNotions.GL3Theta Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3r7

namespace Formalism.MainNotions.Ext.CutA

def SDiffOfGram : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : G1 p) (S : Set (ℂ_[p] × ℂ_[p])), g.Ok →
    (0 : ℂ_[p] × ℂ_[p]) ∈ S → (∀ α ∈ S, α.swap ∈ S) → (∀ α ∈ S, ∀ β ∈ S, α + β ∈ S) → (∀ α ∈ S, ∀ β ∈ S, α * β ∈ S) →
    (∀ (κ : Type) [Fintype κ] (k : ℕ) (A : Fin k → κ → ℂ_[p] × ℂ_[p]), (∀ j i, A j i ∈ S) →
      Simeq (g.PhOn A)
        (∑ j, MvPowerSeries.C (hP (A j) (A j)).1 * g.phAt (Xv j) +
          ∑ j, ∑ j' ∈ Finset.univ.filter (fun j' => j < j'), g.be (g.mulBy (hP (A j) (A j')).1 (Xv j)) (Xv j'))) →
    (∀ α ∈ S, Simeq (g.be (g.mulBy α.1 (Xv 0)) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p])
        (g.be (Xv 0) (g.mulBy α.2 (Xv 1)))) →
    ∀ (κ ι ι' : Type) [Fintype κ] [Fintype ι] [Fintype ι'] (a : ι → κ → ℂ_[p] × ℂ_[p]) (a' : ι' → κ → ℂ_[p] × ℂ_[p]),
      (∀ e k, a e k ∈ S) → (∀ e k, a' e k ∈ S) →
      Simeq (sdL g a a') (sdR g a a') ∧ Simeq (sdL g a a') (sdR' g a a')

def SplitZeroG : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : G1 p) (S : Set (ℂ_[p] × ℂ_[p])), g.Ok → p ≠ 2 →
    (∀ α ∈ S, α.swap ∈ S) →
    (∀ α ∈ S, IntegralMv (g.mulBy α.1 (Xv ()) : MvPowerSeries Unit ℂ_[p])) →
    IntegralMv (g.add (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]) →
    (∀ α ∈ S, Simeq (g.be (g.mulBy α.1 (Xv 0)) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p])
        (g.be (Xv 0) (g.mulBy α.2 (Xv 1)))) →
    Simeq (g.be (g.add (Xv 0) (Xv 1)) (Xv 2) : MvPowerSeries (Fin 3) ℂ_[p])
      (g.be (Xv 0) (Xv 2) + g.be (Xv 1) (Xv 2)) →
    Simeq (g.phAt (g.mulBy (-1) (Xv ())) : MvPowerSeries Unit ℂ_[p]) (g.phAt (Xv ())) →
    (∃ α ∈ S, ∃ a b : ℤ_[p], α = (zc a, zc b) ∧ IsUnit (a - b)) →
    Simeq (g.be (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]) 0 ∧ Simeq (g.phAt (Xv ()) : MvPowerSeries Unit ℂ_[p]) 0

def BeConjOfNorm : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : G1 p) (S : Set (ℂ_[p] × ℂ_[p])), g.Ok →
    (∀ α ∈ S, α.swap ∈ S) → (∀ α ∈ S, ∀ β ∈ S, α + β ∈ S) →
    (∀ α ∈ S, IntegralMv (g.mulBy α.1 (Xv ()) : MvPowerSeries Unit ℂ_[p])) →
    IntegralMv (g.add (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]) →
    (∀ α ∈ S, ∃ n : ℤ_[p], α.1 * α.2 = zc n) →
    (∀ α ∈ S, ∃ β ∈ S, ∃ γ ∈ S, ‖β.1‖ = 1 ∧ ‖γ.1‖ = 1 ∧ α = β + γ) →
    (∀ α ∈ S, Simeq (g.phAt (g.mulBy α.1 (Xv ())) : MvPowerSeries Unit ℂ_[p])
        (MvPowerSeries.C (α.1 * α.2) * g.phAt (Xv ()))) →
    Simeq (g.be (g.add (Xv 0) (Xv 1)) (Xv 2) : MvPowerSeries (Fin 3) ℂ_[p])
      (g.be (Xv 0) (Xv 2) + g.be (Xv 1) (Xv 2)) →
    ∀ α ∈ S, Simeq (g.be (g.mulBy α.1 (Xv 0)) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p])
        (g.be (Xv 0) (g.mulBy α.2 (Xv 1)))

end Formalism.MainNotions.Ext.CutA
