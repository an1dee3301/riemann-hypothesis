module

public import Mathlib
public import Development.Core20Slim.Formalism.PeriodIntegrals.AddIntG
public import Init.Data.Fin.Basic
public import Init.Data.Nat.Basic
public import Init.Data.NeZero
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Instances
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Logic.Basic
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.MvPowerSeries.Inverse
public import Mathlib.RingTheory.MvPowerSeries.Substitution
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

namespace PI.AddIntG.Wk

variable {p : ℕ} [Fact p.Prime]

def G (W : WeierstrassCurve ℂ_[p]) {R : Type*} [CommRing R] [Algebra ℂ_[p] R] (u v : R) : R :=
  u ^ 3 + algebraMap ℂ_[p] R W.a₁ * u * v + algebraMap ℂ_[p] R W.a₂ * u ^ 2 * v +
    algebraMap ℂ_[p] R W.a₃ * v ^ 2 + algebraMap ℂ_[p] R W.a₄ * u * v ^ 2 +
    algebraMap ℂ_[p] R W.a₆ * v ^ 3 - v

def Gu (W : WeierstrassCurve ℂ_[p]) {R : Type*} [CommRing R] [Algebra ℂ_[p] R] (u v : R) : R :=
  3 * u ^ 2 + algebraMap ℂ_[p] R W.a₁ * v + 2 * algebraMap ℂ_[p] R W.a₂ * u * v +
    algebraMap ℂ_[p] R W.a₄ * v ^ 2

def Gv (W : WeierstrassCurve ℂ_[p]) {R : Type*} [CommRing R] [Algebra ℂ_[p] R] (u v : R) : R :=
  algebraMap ℂ_[p] R W.a₁ * u + algebraMap ℂ_[p] R W.a₂ * u ^ 2 + 2 * algebraMap ℂ_[p] R W.a₃ * v +
    2 * algebraMap ℂ_[p] R W.a₄ * u * v + 3 * algebraMap ℂ_[p] R W.a₆ * v ^ 2 - 1

def wser (wq : PowerSeries ℂ_[p]) : PowerSeries ℂ_[p] := PowerSeries.X ^ 3 * wq

def wv (wq : PowerSeries ℂ_[p]) (i : Fin 2) : MvPowerSeries (Fin 2) ℂ_[p] :=
  PowerSeries.subst (Xv i : MvPowerSeries (Fin 2) ℂ_[p]) (wser wq)

def lam (wq : PowerSeries ℂ_[p]) : MvPowerSeries (Fin 2) ℂ_[p] :=
  fun e => PowerSeries.coeff (e 0 + e 1 + 1) (wser wq)

def nu (wq : PowerSeries ℂ_[p]) : MvPowerSeries (Fin 2) ℂ_[p] :=
  wv wq 0 - lam wq * Xv 0

abbrev cc (a : ℂ_[p]) : MvPowerSeries (Fin 2) ℂ_[p] := algebraMap ℂ_[p] (MvPowerSeries (Fin 2) ℂ_[p]) a

def Acf (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) : MvPowerSeries (Fin 2) ℂ_[p] :=
  1 + cc W.a₂ * lam wq + cc W.a₄ * lam wq ^ 2 + cc W.a₆ * lam wq ^ 3

def Bcf (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) : MvPowerSeries (Fin 2) ℂ_[p] :=
  cc W.a₁ * lam wq + cc W.a₂ * nu wq + cc W.a₃ * lam wq ^ 2 + 2 * cc W.a₄ * lam wq * nu wq +
    3 * cc W.a₆ * lam wq ^ 2 * nu wq

def Ccf (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) : MvPowerSeries (Fin 2) ℂ_[p] :=
  cc W.a₁ * nu wq + 2 * cc W.a₃ * lam wq * nu wq + cc W.a₄ * nu wq ^ 2 +
    3 * cc W.a₆ * lam wq * nu wq ^ 2 - lam wq

def Dcf (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) : MvPowerSeries (Fin 2) ℂ_[p] :=
  cc W.a₃ * nu wq ^ 2 + cc W.a₆ * nu wq ^ 3 - nu wq

def Z3 (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) : MvPowerSeries (Fin 2) ℂ_[p] :=
  -Xv 0 - Xv 1 - Bcf W wq * (Acf W wq)⁻¹

def Fch (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) : MvPowerSeries (Fin 2) ℂ_[p] :=
  MvPowerSeries.subst (fun i : Fin 2 => if i = 0 then (0 : MvPowerSeries (Fin 2) ℂ_[p]) else Z3 W wq) (Z3 W wq)

end PI.AddIntG.Wk
