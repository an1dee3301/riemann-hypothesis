module

public import Mathlib
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.RepresentationTheory.Basic

@[expose] public section

noncomputable def UpperTheory.Reformulated.B.CyclicSubtraction.cycSub.{u_1, u_2} :
    {G : Type u_1} → {M : Type u_2} → [inst : Group G] → [inst_1 : AddCommGroup M] → Representation ℤ G M → G → M →+ M :=
    fun {G : Type u_1} {M : Type u_2} [Group G] [AddCommGroup M] (ρ : Representation ℤ G M) (σ : G) ↦
      ((ρ : G → M →ₗ[ℤ] M) σ - LinearMap.id).toAddMonoidHom

theorem UpperTheory.Reformulated.B.CyclicSubtraction.apply_eq_of_cycSub_eq_zero.{u_1, u_2} :
    ∀ {G : Type u_1} {M : Type u_2} [inst : Group G] [inst_1 : AddCommGroup M] (ρ : Representation ℤ G M) {σ : G},
      (∀ (g : G), g ∈ Subgroup.zpowers σ) →
        ∀ {x : M}, (UpperTheory.Reformulated.B.CyclicSubtraction.cycSub ρ σ : M → M) x = (0 : M) → ∀ (g : G), ((ρ : G → M →ₗ[ℤ] M) g : M → M) x = x := by
  intro G M _ _ ρ σ hσ x hx g
  have h0 : ρ σ x - x = 0 := hx
  have h1 : ρ σ x = x := sub_eq_zero.mp h0
  let H : Subgroup G :=
    { carrier := {g | ρ g x = x}
      one_mem' := by
        show ρ 1 x = x
        rw [map_one]
        rfl
      mul_mem' := by
        intro a b ha hb
        have ha' : ρ a x = x := ha
        have hb' : ρ b x = x := hb
        show ρ (a * b) x = x
        rw [map_mul, Module.End.mul_apply, hb', ha']
      inv_mem' := by
        intro a ha
        have ha' : ρ a x = x := ha
        show ρ a⁻¹ x = x
        calc ρ a⁻¹ x = ρ a⁻¹ (ρ a x) := by rw [ha']
          _ = ρ (a⁻¹ * a) x := by rw [map_mul, Module.End.mul_apply]
          _ = x := by
            rw [inv_mul_cancel, map_one]
            rfl }
  have hle : Subgroup.zpowers σ ≤ H := (Subgroup.zpowers_le).mpr h1
  exact hle (hσ g)
