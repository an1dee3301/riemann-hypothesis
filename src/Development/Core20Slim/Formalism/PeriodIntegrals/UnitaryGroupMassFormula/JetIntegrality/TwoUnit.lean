module

public import Mathlib
public import Development.Core20Slim.Formalism.PeriodIntegrals.JetsPhW
public import Init.Core
public import Init.Data.Fin.Basic
public import Init.Data.Nat.Basic
public import Init.Data.NeZero
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Instances
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Logic.Basic
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.Logic.Function.Iterate
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.MvPowerSeries.Derivative
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

namespace PI.JetsPhW.W

open PI.JetsPhW

def Dv {p : ℕ} [Fact p.Prime] {σ : Type*} (v : PowerSeries ℂ_[p]) (i : σ)
    (f : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] :=
  PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries σ ℂ_[p]) v * MvPowerSeries.pderiv (R := ℂ_[p]) i f

def psi {p : ℕ} [Fact p.Prime] (ex ph : PowerSeries ℂ_[p]) : PowerSeries ℂ_[p] :=
  PowerSeries.subst ex ph

def IntP {p : ℕ} [Fact p.Prime] (g : PowerSeries ℂ_[p]) : Prop :=
  ∀ n, IsIntP (PowerSeries.coeff n g)

def DChain : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ : Type) (i : σ) (l v g : PowerSeries ℂ_[p]) (s : MvPowerSeries σ ℂ_[p])
    (c : ℂ_[p]), v * dX l = 1 → MvPowerSeries.constantCoeff s = 0 →
    MvPowerSeries.pderiv (R := ℂ_[p]) i s =
      MvPowerSeries.C c * PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries σ ℂ_[p]) (dX l) →
    Dv v i (PowerSeries.subst s g) = MvPowerSeries.C c * PowerSeries.subst s (dX g)

def PdSelf : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ : Type) (i : σ) (g : PowerSeries ℂ_[p]),
    MvPowerSeries.pderiv (R := ℂ_[p]) i (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries σ ℂ_[p]) g) =
      PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries σ ℂ_[p]) (dX g)

def PdNe : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ : Type) (i j : σ) (g : PowerSeries ℂ_[p]), j ≠ i →
    MvPowerSeries.pderiv (R := ℂ_[p]) i (PowerSeries.subst (MvPowerSeries.X j : MvPowerSeries σ ℂ_[p]) g) = 0

def DSelf : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ : Type) (i : σ) (v g : PowerSeries ℂ_[p]),
    Dv v i (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries σ ℂ_[p]) g) =
      PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries σ ℂ_[p]) (v * dX g)

def Ev0 : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ : Type) (s : MvPowerSeries σ ℂ_[p]) (g : PowerSeries ℂ_[p]),
    MvPowerSeries.constantCoeff s = 0 →
    MvPowerSeries.constantCoeff (PowerSeries.subst s g) = PowerSeries.constantCoeff g

def JetD : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (ex ph : PowerSeries ℂ_[p]) (n : ℕ),
    jet ex ph n = PowerSeries.constantCoeff ((dX (A := ℂ_[p]))^[n] (psi ex ph))

def LogDer : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ : Type) (i : σ) (v : PowerSeries ℂ_[p]) (f : MvPowerSeries σ ℂ_[p]),
    IntP v → MvPowerSeries.constantCoeff f = 0 → IntegralMv (expMv f) → IntegralMv (Dv v i f)

def Dint : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ : Type) (i : σ) (v : PowerSeries ℂ_[p]) (f : MvPowerSeries σ ℂ_[p]),
    IntP v → IntegralMv f → IntegralMv (Dv v i f)

abbrev lX {p : ℕ} [Fact p.Prime] {σ : Type*} (l : PowerSeries ℂ_[p]) (j : σ) : MvPowerSeries σ ℂ_[p] :=
  PowerSeries.subst (MvPowerSeries.X j : MvPowerSeries σ ℂ_[p]) l

def Rw3 : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (l ex ph : PowerSeries ℂ_[p]), LogOk l ex →
    cubeE l ex ph =
      PowerSeries.subst (lX l 0 + lX l 1 + lX l 2 : MvPowerSeries (Fin 3) ℂ_[p]) (psi ex ph) -
        PowerSeries.subst (lX l 0 + lX l 1 : MvPowerSeries (Fin 3) ℂ_[p]) (psi ex ph) -
        PowerSeries.subst (lX l 1 + lX l 2 : MvPowerSeries (Fin 3) ℂ_[p]) (psi ex ph) -
        PowerSeries.subst (lX l 2 + lX l 0 : MvPowerSeries (Fin 3) ℂ_[p]) (psi ex ph) +
        phAt ph (Xv 0) + phAt ph (Xv 1) + phAt ph (Xv 2)

end PI.JetsPhW.W
