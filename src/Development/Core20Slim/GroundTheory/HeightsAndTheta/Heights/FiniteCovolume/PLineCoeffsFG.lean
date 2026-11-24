module

public import Mathlib
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.SecondCountableTopologyArchUnitary
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.MajorantInvolutionDiagonalForm
public import Init.Core
public import Init.Data.Function
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.EuclideanDomain.Int
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Hom.Instances
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.End
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Module.Submodule.Map
public import Mathlib.Algebra.Module.Torsion.Free
public import Mathlib.Algebra.NoZeroSMulDivisors.Basic
public import Mathlib.Algebra.NoZeroSMulDivisors.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.GroupTheory.Finiteness
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Hom.Basic
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.RingTheory.PrincipalIdealDomain
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal

@[expose] public section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

noncomputable section

variable {E : Type*} [Field E]
variable (W : Type*) [AddCommGroup W] [Module E W]

theorem LineCoeffsFG.proof : LineCoeffsFG.Statement (E := E) W := by
  intro La x hLa hx
  let f : E →+ W := (smulAddHom E W).flip x
  have hf : Function.Injective f.toIntLinearMap := by
    intro a b hab
    have h : a • x = b • x := hab
    exact smul_left_injective E hx h
  have hS : La.toIntSubmodule.FG := by
    rw [Submodule.fg_iff_addSubgroup_fg]
    simpa using hLa
  have hle : (lineCoeffs (E := E) La x).toIntSubmodule.map f.toIntLinearMap ≤
      La.toIntSubmodule := by
    rintro _ ⟨a, ha, rfl⟩
    exact ha
  have hN : (lineCoeffs (E := E) La x).toIntSubmodule.FG :=
    Submodule.fg_of_fg_map_injective _ hf (hS.of_le hle)
  rw [Submodule.fg_iff_addSubgroup_fg] at hN
  simpa using hN

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
