module

public import Mathlib
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StTraceHermNondegenerate
public import Development.Core20Slim.GroundTheory.AutomorphicForms.HermitianSpaces
public import Development.Core20Slim.GroundTheory.AutomorphicForms.QuadraticConj
public import Init.Core
public import Init.Data.Function
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Rat.Defs
public import Mathlib.FieldTheory.Perfect
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.LinearAlgebra.SesquilinearForm.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Trace.Basic
public import Mathlib.RingTheory.Trace.Defs

@[expose] public section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module

variable {F E : Type*} [Field F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι]


omit [NumberField E] in
theorem HermitianForm.eq_zero_of_toSesq_eq_zero (h : HermitianForm F E W) {x : W}
    (hx : ∀ w, h.toSesq x w = 0) : x = 0 := by
  apply h.nonsingular.1
  rw [map_zero]
  exact LinearMap.ext hx

theorem TraceHermNondegenerate.proof (h : HermitianForm F E W) (v : Basis ι E W) :
    TraceHermNondegenerate.Statement h v := by
  have hT := (traceForm_nondegenerate ℚ E).1
  constructor
  · intro y hy
    have key : ∀ w, h.toSesq (v.equivFun.symm y) w = 0 := by
      intro w
      apply hT
      intro a
      have := hy (v.equivFun (a • w))
      rw [traceHerm_apply, LinearEquiv.symm_apply_apply, LinearMap.map_smul, smul_eq_mul] at this
      rw [Algebra.traceForm_apply, mul_comm]
      exact this
    have h0 := HermitianForm.eq_zero_of_toSesq_eq_zero h key
    exact (map_eq_zero_iff _ v.equivFun.symm.injective).1 h0
  · intro z hz
    have key : ∀ w, h.toSesq w (v.equivFun.symm z) = 0 := by
      intro w
      apply hT
      intro a
      have := hz (v.equivFun (conj F E a • w))
      rw [traceHerm_apply, LinearEquiv.symm_apply_apply, LinearMap.map_smulₛₗ₂, smul_eq_mul] at this
      rw [Algebra.traceForm_apply, mul_comm]
      simpa [conj_conj] using this
    have key' : ∀ w, h.toSesq (v.equivFun.symm z) w = 0 := by
      intro w
      have e := (LinearMap.isSymm_def.1 h.isSymm) (v.equivFun.symm z) w
      rw [key w] at e
      exact (map_eq_zero_iff _ (conjHom F E).injective).1 e
    have h0 := HermitianForm.eq_zero_of_toSesq_eq_zero h key'
    exact (map_eq_zero_iff _ v.equivFun.symm.injective).1 h0

end GroundTheory.Heights₂.Heights.FiniteCovolume
