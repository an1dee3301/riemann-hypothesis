module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.LatticeFrames.SplitPart
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
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
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MovedVac

theorem halfBack : ∀ (D : D7) (S T : HSp D) (g : GA D S) (h : GA D T) (e : AE D) (u : WO S T),
    IsHalf e (actO S T g h u) → IsHalf e u := by
  intro D S T g h e u hu
  have hA : Formalism.L2.Theta.mt T h⁻¹ * Formalism.L2.Theta.mt T h = 1 := by
    simp only [Formalism.L2.Theta.mt, map_inv]
    exact congrArg Units.val (inv_mul_cancel (matHom T h))
  have hB : Formalism.L2.Theta.mt S g⁻¹ * Formalism.L2.Theta.mt S g = 1 := by
    simp only [Formalism.L2.Theta.mt, map_inv]
    exact congrArg Units.val (inv_mul_cancel (matHom S g))
  have cancel : ∀ X : Matrix (Fin T.rank) (Fin S.rank) (AE D),
      HMul.hMul (HMul.hMul (Formalism.L2.Theta.mt T h⁻¹) (HMul.hMul (HMul.hMul (Formalism.L2.Theta.mt T h) X)
        (Formalism.L2.Theta.mt S g⁻¹))) (Formalism.L2.Theta.mt S g) = X := by
    intro X
    simp only [Matrix.mul_assoc, hB, Matrix.mul_one]
    rw [← Matrix.mul_assoc, hA, Matrix.one_mul]
  have key : e • actO S T g h u = actO S T g h u := by
    ext i j; exact hu i j
  have key2 : e • u = u := by
    have h1 := congrArg (fun M : Matrix (Fin T.rank) (Fin S.rank) (AE D) =>
      HMul.hMul (HMul.hMul (Formalism.L2.Theta.mt T h⁻¹) M) (Formalism.L2.Theta.mt S g)) key
    simp only [actO] at h1
    rw [cancel u] at h1
    simp only [Matrix.mul_smul, Matrix.smul_mul] at h1
    rw [cancel u] at h1
    exact h1
  intro i j
  have := congrFun (congrFun key2 i) j
  rw [Matrix.smul_apply, smul_eq_mul] at this
  exact this







end GlobalTheory.MovedVac
