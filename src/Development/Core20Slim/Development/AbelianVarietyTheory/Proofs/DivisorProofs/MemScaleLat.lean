module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodModModT
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

open NumberField MeasureTheory IsDedekindDomain UniqueFactorizationMonoid
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum
open GlobalTheory.SqTop (modT)
open GlobalTheory.BottomIPData (sfB)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl Lat IsFockVec IsSphOff volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip)
open GlobalTheory.Core.Rk.IP (openOff integrand wcoef)
open GlobalTheory.StdLoc (glVol blockIdx)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.NormRatio

noncomputable section

namespace GlobalTheory.NormRatio

variable {D : D7}

def scaleInv (D : D7) (r : D.host.E) : Submodule (𝓞 D.host.E) D.host.E where
  carrier := {x | ∀ c ∈ D.host.ccE, r * (c : D.host.E) * x ∈ (1 : Submodule (𝓞 D.host.E) D.host.E)}
  add_mem' := by
    intro x y hx hy c hc
    rw [mul_add]
    exact add_mem (hx c hc) (hy c hc)
  zero_mem' := by
    intro c _
    rw [mul_zero]
    exact zero_mem _
  smul_mem' := by
    intro b x hx c hc
    have h : r * (c : D.host.E) * (b • x) = b • (r * (c : D.host.E) * x) := by
      rw [Algebra.smul_def, Algebra.smul_def]; ring
    rw [h]
    exact Submodule.smul_mem _ b (hx c hc)

def scaleLat (D : D7) (r : D.host.E) (n : ℕ) : Submodule (𝓞 D.host.E) (Fin n → D.host.E) :=
  Submodule.pi Set.univ fun _ => scaleInv D r

theorem mem_scaleLat {r : D.host.E} {n : ℕ} {y : Fin n → D.host.E} :
    y ∈ scaleLat D r n ↔ ∀ i, ∀ c ∈ D.host.ccE, r * (c : D.host.E) * y i ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) := by
  simp only [scaleLat, Submodule.mem_pi, Set.mem_univ, true_implies]
  rfl

end GlobalTheory.NormRatio
