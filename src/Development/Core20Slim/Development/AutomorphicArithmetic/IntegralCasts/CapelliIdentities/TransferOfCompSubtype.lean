module

public import Mathlib
public import Init.Classical
public import Init.Core
public import Init.Prelude
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Quotient
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Quot
public import Mathlib.Data.ZMod.QuotientGroup
public import Mathlib.Dynamics.PeriodicPts.Defs
public import Mathlib.GroupTheory.Abelianization.Defs
public import Mathlib.GroupTheory.Coset.Defs
public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.Transfer

@[expose] public section

theorem UpperTheory.Reformulated.B.Qe30.transfer_of_comp_subtype.{u_1} :
    ∀ {Γ : Type u_1} [inst : Group Γ] (H : Subgroup Γ)
    [inst_1 : H.FiniteIndex] (g : Γ),
    ((Abelianization.of.comp H.subtype).transfer : Γ → Abelianization Γ) g =
      (Abelianization.of : Γ → Abelianization Γ) g ^ H.index := by
  intro Γ _ H _ g
  classical
  let _ := H.fintypeQuotientOfFiniteIndex
  rw [MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot,
    Subgroup.index_eq_sum_minimalPeriod H g, ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_congr rfl fun q _ => ?_
  rw [MonoidHom.comp_apply, Subgroup.subtype_apply, map_mul, map_mul, map_inv, map_pow,
    inv_mul_cancel_comm]
