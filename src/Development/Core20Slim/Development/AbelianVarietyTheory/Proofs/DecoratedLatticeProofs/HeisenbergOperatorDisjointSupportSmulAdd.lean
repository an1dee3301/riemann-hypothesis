module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FinTensMemLatO
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.GroupWithZero.Action
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Trace.Defs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer
open IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeisDisj

variable {D : D7}

theorem cA_smul (c : AF D.host.F) (z : AE D) : cA D (c • z) = c • cA D z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => rw [TensorProduct.smul_tmul']; rfl
  | add a b ha hb => rw [smul_add, map_add (f := _), map_add (f := _), ha, hb, smul_add]

theorem hO_add_left (S T : HSp D) (x x' y : WO S T) : hO S T (x + x') y = hO S T x y + hO S T x' y := by
  simp only [hO, Matrix.add_apply, mul_add, Finset.sum_add_distrib]

theorem hO_add_right (S T : HSp D) (x y y' : WO S T) : hO S T x (y + y') = hO S T x y + hO S T x y' := by
  simp only [hO, Matrix.add_apply, map_add (f := _), mul_add, add_mul, Finset.sum_add_distrib]

theorem hO_smul_smul (S T : HSp D) (c c' : AF D.host.F) (x y : WO S T) :
    hO S T (c • x) (c' • y) = (c * c') • hO S T x y := by
  simp only [hO, Matrix.smul_apply, cA_smul, Finset.smul_sum, mul_smul_comm, smul_mul_assoc, smul_smul]

theorem symplOH_add_left (S T : HSp D) (x x' y : WO S T) :
    symplOH S T (x + x') y = symplOH S T x y + symplOH S T x' y := by
  simp only [symplOH, symplO, hO_add_left, mul_add, map_add (f := _)]

theorem symplOH_add_right (S T : HSp D) (x y y' : WO S T) :
    symplOH S T x (y + y') = symplOH S T x y + symplOH S T x y' := by
  simp only [symplOH, symplO, hO_add_right, mul_add, map_add (f := _)]

theorem symplOH_smul_smul_eq_zero (S T : HSp D) (c c' : AF D.host.F) (x y : WO S T) (h : c * c' = 0) :
    symplOH S T (c • x) (c' • y) = 0 := by
  rw [symplOH, symplO, hO_smul_smul, h, zero_smul, mul_zero, map_zero, mul_zero]

theorem heisO_smul_add_smul : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (c c' : AF D.host.F) (x y : WO S T) (f : WO S T → ℂ), c * c' = 0 → heisO ψ S T (c • x + c' • y) f = heisO ψ S T (c • x) (heisO ψ S T (c' • y) f) := by
  intro D ψ S T c c' x y f h
  funext w
  simp only [heisO]
  rw [symplOH_add_right, symplOH_add_left, symplOH_smul_smul_eq_zero S T c c' x y h, add_zero,
    AddChar.map_add_eq_mul, add_assoc, mul_assoc]

end GlobalTheory.HeisDisj
