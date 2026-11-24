module

public import Mathlib
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.SecondCountableTopologyArchUnitary
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.MajorantInvolutionDiagonalForm
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Objects
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Finsupp.SMul
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.RingTheory.SimpleRing.Basic

@[expose] public section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open Module NumberField

variable {E : Type*} [Field E] {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*}

theorem VecAtNeZero.proof (v : Basis ι E W) : VecAtNeZero.Statement v := by
  intro x hx w hw
  apply hx
  apply v.repr.injective
  ext i
  have h := congrFun hw i
  simp only [vecAt, Pi.zero_apply] at h
  simpa using (map_eq_zero_iff w.embedding w.embedding.injective).mp h

end GroundTheory.Heights₂.Heights.FiniteCovolume
