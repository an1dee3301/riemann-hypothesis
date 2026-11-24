module

public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.PlaceS
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
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum

namespace Formalism.IndefR.Fin.LevelGroupLemmas

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem mt_mul' (V : HSp D) (a b : GA D V) : Formalism.L2.Theta.mt V (a * b) = Formalism.L2.Theta.mt V a * Formalism.L2.Theta.mt V b := by
  simp [Formalism.L2.Theta.mt, map_mul, Units.val_mul]

theorem mt_one' (V : HSp D) : Formalism.L2.Theta.mt V (1 : GA D V) = 1 := by
  simp [Formalism.L2.Theta.mt, map_one, Units.val_one]

theorem actO_eq {S T : HSp D} (g : GA D S) (h : GA D T) (x : WO S T) :
    actO S T g h x = HMul.hMul (HMul.hMul (Formalism.L2.Theta.mt T h) x) (Formalism.L2.Theta.mt S g⁻¹) := rfl

theorem actO_actO {S T : HSp D} (g g' : GA D S) (h h' : GA D T) (x : WO S T) :
    actO S T g h (actO S T g' h' x) = actO S T (g * g') (h * h') x := by
  rw [actO_eq, actO_eq, actO_eq, _root_.mul_inv_rev, mt_mul', mt_mul']
  simp only [Matrix.mul_assoc]

theorem actO_one {S T : HSp D} (x : WO S T) : actO S T 1 1 x = x := by
  rw [actO_eq, inv_one, mt_one', mt_one', Matrix.one_mul, Matrix.mul_one]



theorem isHalf_mul_mul {e : AE D} {a b c : ℕ} (M : Matrix (Fin a) (Fin b) (AE D)) (x : Matrix (Fin b) (Fin c) (AE D))
    (N : Matrix (Fin c) (Fin c) (AE D)) (hx : IsHalf e x) : IsHalf e (M * x * N) := by
  intro i j
  simp only [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
  conv_rhs => rw [← hx k l]
  ring

theorem isHalf_actO {S T : HSp D} {e : AE D} (g : GA D S) (h : GA D T) (x : WO S T) :
    IsHalf e (actO S T g h x) ↔ IsHalf e x := by
  constructor
  · intro hx
    have : actO S T g⁻¹ h⁻¹ (actO S T g h x) = x := by
      rw [actO_actO, inv_mul_cancel, inv_mul_cancel, actO_one]
    rw [← this]
    exact isHalf_mul_mul _ _ _ hx
  · intro hx
    exact isHalf_mul_mul _ _ _ hx


end Formalism.IndefR.Fin.LevelGroupLemmas

end
