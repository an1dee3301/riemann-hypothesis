module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

set_option maxHeartbeats 800000

noncomputable section

namespace GlobalTheory.AdjLatO

variable {D : D7}

theorem incA_mul_tmul' (g e : D.host.E) (x : AF D.host.F) :
    incA D g * (x ⊗ₜ[D.host.F] e) = x ⊗ₜ[D.host.F] (g * e) := by
  change ((1 : AF D.host.F) ⊗ₜ[D.host.F] g) * _ = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]

theorem tmul_mul_incA' (g e : D.host.E) (x : AF D.host.F) :
    (x ⊗ₜ[D.host.F] e) * incA D g = x ⊗ₜ[D.host.F] (e * g) := by
  change _ * ((1 : AF D.host.F) ⊗ₜ[D.host.F] g) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]

def tensM (x : AF D.host.F) {m n : ℕ} (M : Matrix (Fin m) (Fin n) D.host.E) : Mx D m n :=
  M.map fun e => x ⊗ₜ[D.host.F] e

theorem rat_mul_tensM (x : AF D.host.F) {l m n : ℕ} (G : Matrix (Fin l) (Fin m) D.host.E)
    (M : Matrix (Fin m) (Fin n) D.host.E) : rat G ⬝ tensM x M = tensM x (G * M) := by
  ext i j
  simp only [tensM, rat, Matrix.mul_apply, Matrix.map_apply, incA_mul_tmul', TensorProduct.tmul_sum]

theorem tensM_mul_rat (x : AF D.host.F) {l m n : ℕ} (M : Matrix (Fin l) (Fin m) D.host.E)
    (G : Matrix (Fin m) (Fin n) D.host.E) : tensM x M ⬝ rat G = tensM x (M * G) := by
  ext i j
  simp only [tensM, rat, Matrix.mul_apply, Matrix.map_apply, tmul_mul_incA', TensorProduct.tmul_sum]









end GlobalTheory.AdjLatO
