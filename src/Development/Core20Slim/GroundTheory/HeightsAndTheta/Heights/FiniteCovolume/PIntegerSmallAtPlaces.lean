module

public import Mathlib
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.SecondCountableTopologyArchUnitary
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.MajorantInvolutionDiagonalForm
public import Init.Classical
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Nonempty
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

@[expose] public section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField

theorem IntegerSmallAtPlaces.proof (E : Type*) [Field E] [NumberField E] :
    IntegerSmallAtPlaces.Statement E := by
  intro a ha hlt
  by_contra hne
  let b : 𝓞 E := ⟨a, ha⟩
  have hb : b ≠ 0 := fun h => hne (congrArg Subtype.val h)
  let w : InfinitePlace E := Classical.arbitrary _
  have h1 : 1 ≤ w b := InfinitePlace.one_le_of_lt_one hb (fun z _ => hlt z)
  exact absurd (hlt w) (not_lt.mpr h1)

end GroundTheory.Heights₂.Heights.FiniteCovolume
