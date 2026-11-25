module

public import Mathlib
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.SecondCountableTopologyArchUnitary
public import Development.Core20Slim.GroundTheory.AutomorphicForms.HermitianSpaces
public import Init.Core
public import Init.Data.Rat.Basic
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Rat
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.LinearAlgebra.InvariantBasisNumber
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Trace.Defs

@[expose] public section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι]

def traceHerm (h : HermitianForm F E W) (v : Basis ι E W) : LinearMap.BilinForm ℚ (ι → E) :=
  LinearMap.mk₂ ℚ
    (fun y z => Algebra.trace ℚ E (h.toSesq (v.equivFun.symm y) (v.equivFun.symm z)))
    (fun y₁ y₂ z => by simp only [map_add (f := _), LinearMap.add_apply])
    (fun c y z => by
      have e1 : v.equivFun.symm (c • y) = (algebraMap ℚ E c) • v.equivFun.symm y := by
        rw [← LinearEquiv.map_smul, algebraMap_smul]
      have e2 : conjHom F E (algebraMap ℚ E c) = algebraMap ℚ E c :=
        RingHom.map_rat_algebraMap _ _
      rw [e1, LinearMap.map_smulₛₗ₂, e2, smul_eq_mul, ← Algebra.smul_def, LinearMap.map_smul,
        smul_eq_mul])
    (fun y z₁ z₂ => by simp only [map_add (f := _)])
    (fun c y z => by
      have e1 : v.equivFun.symm (c • z) = (algebraMap ℚ E c) • v.equivFun.symm z := by
        rw [← LinearEquiv.map_smul, algebraMap_smul]
      rw [e1, LinearMap.map_smul, smul_eq_mul, ← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul])

theorem traceHerm_apply (h : HermitianForm F E W) (v : Basis ι E W) (y z : ι → E) :
    traceHerm h v y z = Algebra.trace ℚ E (h.toSesq (v.equivFun.symm y) (v.equivFun.symm z)) := rfl

def TraceHermNondegenerate.Statement (h : HermitianForm F E W) (v : Basis ι E W) : Prop :=
  (traceHerm h v).Nondegenerate

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
