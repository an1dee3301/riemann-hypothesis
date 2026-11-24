module

public import Mathlib
public import Init.Data.Cast
public import Init.Data.Fin.Basic
public import Init.Data.Nat.Basic
public import Init.Data.NeZero
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
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
public import Mathlib.Data.Finset.Range
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.PowerSeries.Substitution
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.GroupCompletion
public import Mathlib.Topology.Algebra.IsUniformGroup.Defs
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.UniformField
public import Mathlib.Topology.Algebra.UniformRing
public import Mathlib.Topology.Algebra.Valued.ValuationTopology
public import Mathlib.Topology.Algebra.Valued.ValuedField
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

open Classical

namespace PI.BiaddOfCube

def IsIntP {p : ℕ} [Fact p.Prime] (x : ℂ_[p]) : Prop := ‖x‖ ≤ 1

def IntegralMv {σ : Type*} {p : ℕ} [Fact p.Prime] (F : MvPowerSeries σ ℂ_[p]) : Prop :=
  ∀ n, IsIntP (MvPowerSeries.coeff n F)

def expMv {σ : Type*} {p : ℕ} [Fact p.Prime] (F : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] :=
  fun α => ∑ n ∈ Finset.range ((α.sum fun _ k => k) + 1),
    MvPowerSeries.coeff α (F ^ n) / (n.factorial : ℂ_[p])

def Simeq {σ : Type*} {p : ℕ} [Fact p.Prime] (f g : MvPowerSeries σ ℂ_[p]) : Prop :=
  MvPowerSeries.constantCoeff (f - g) = 0 ∧ IntegralMv (expMv (f - g))

abbrev Xv {p : ℕ} [Fact p.Prime] {σ : Type*} (i : σ) : MvPowerSeries σ ℂ_[p] := MvPowerSeries.X i

variable {p : ℕ} [Fact p.Prime] {σ : Type*} (l ex ph : PowerSeries ℂ_[p])

def add (a b : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] :=
  PowerSeries.subst (PowerSeries.subst a l + PowerSeries.subst b l) ex

def phAt (a : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] := PowerSeries.subst a ph

def be (a b : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] :=
  phAt ph (add l ex a b) - phAt ph a - phAt ph b

def Target : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (l ex ph : PowerSeries ℂ_[p]),
    PowerSeries.constantCoeff ex = 0 → PowerSeries.subst ex l = PowerSeries.X →
    Simeq (phAt ph (add l ex (add l ex (Xv 0) (Xv 1)) (Xv 2)) - phAt ph (add l ex (Xv 0) (Xv 1)) -
        phAt ph (add l ex (Xv 1) (Xv 2)) - phAt ph (add l ex (Xv 2) (Xv 0)) +
        phAt ph (Xv 0) + phAt ph (Xv 1) + phAt ph (Xv 2) : MvPowerSeries (Fin 3) ℂ_[p]) 0 →
    Simeq (be l ex ph (add l ex (Xv 0) (Xv 1)) (Xv 2) : MvPowerSeries (Fin 3) ℂ_[p])
      (be l ex ph (Xv 0) (Xv 2) + be l ex ph (Xv 1) (Xv 2)) ∧
    Simeq (be l ex ph (Xv 0) (add l ex (Xv 1) (Xv 2)) : MvPowerSeries (Fin 3) ℂ_[p])
      (be l ex ph (Xv 0) (Xv 1) + be l ex ph (Xv 0) (Xv 2))

end PI.BiaddOfCube
