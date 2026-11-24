module

public import Mathlib
public import Formalism.LocalToGlobal.UnitaryNorms.MemFIffReal
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Rat.Basic
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Order.Kleene
public import Mathlib.Algebra.Ring.Action.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Subtype
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.Ideal.Pointwise
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Host Formalism.FrobeniusOrbits
open scoped Pointwise

namespace GlobalTheory.PlaceOverPair

theorem under_smul_of_fix {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K] [Algebra K E]
    (σ : E ≃ₐ[ℚ] E) (h : ∀ x : K, σ (algebraMap K E x) = algebraMap K E x) (I : Ideal (𝓞 E)) :
    (σ • I).under (𝓞 K) = I.under (𝓞 K) := by
  ext x
  rw [Ideal.under_def, Ideal.under_def, Ideal.mem_comap, Ideal.mem_comap, Ideal.mem_pointwise_smul_iff_inv_smul_mem]
  have : σ⁻¹ • algebraMap (𝓞 K) (𝓞 E) x = algebraMap (𝓞 K) (𝓞 E) x := by
    rw [inv_smul_eq_iff]
    apply Subtype.val_injective
    exact (h x).symm
  rw [this]



variable {R : Ranks} (H : Formalism.BasicNotions.Host R)





end GlobalTheory.PlaceOverPair
