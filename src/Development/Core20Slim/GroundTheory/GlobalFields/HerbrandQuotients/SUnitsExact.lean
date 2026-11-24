module

public import Mathlib
public import Development.Core20Slim.GroundTheory.TateCohomology.HerbrandAbstract
public import Development.Core20Slim.GroundTheory.GlobalFields.HerbrandQuotients.Cyclic
public import Development.Core20Slim.GroundTheory.GlobalFields.HerbrandQuotients.CycTate
public import Development.Core20Slim.GroundTheory.LocalFields.HerbrandLocalBase
public import Init.Core
public import Init.Data.Function
public import Init.Data.Int.Basic
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Ext
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Module.Prod
public import Mathlib.Algebra.Quotient
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Image
public import Mathlib.Data.Set.Operations
public import Mathlib.GroupTheory.Coset.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.GroupTheory.Index
public import Mathlib.Order.Notation
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.RingTheory.Finiteness.Defs

@[expose] public section

namespace GroundTheory.Global

open GroundTheory.GroupCoh

variable {G A B C : Type*} [Group G] [Fintype G] [AddCommGroup A] [AddCommGroup B]
  [AddCommGroup C]

theorem hasHerbrandQuotient_cycSubOne_of_finite [Module.Finite ℤ A] (ρ : Representation ℤ G A)
    {σ : G} (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    HasHerbrandQuotient (cycSubOne ρ σ) (cycNorm ρ) :=
  hasCyclicHerbrand_of_finite ρ hσ

theorem cycHerbrand_eq_mul_of_exact (ρA : Representation ℤ G A) (ρB : Representation ℤ G B)
    (ρC : Representation ℤ G C) (σ : G) {i : A →+ B} {p : B →+ C} (hi : Function.Injective i)
    (hex : Function.Exact i p) [Finite (C ⧸ p.range)]
    (hiG : ∀ g a, i (ρA g a) = ρB g (i a)) (hpG : ∀ g b, p (ρB g b) = ρC g (p b))
    (hA : HasHerbrandQuotient (cycSubOne ρA σ) (cycNorm ρA))
    (hC : HasHerbrandQuotient (cycSubOne ρC σ) (cycNorm ρC)) :
    cycHerbrand ρB σ = cycHerbrand ρA σ * cycHerbrand ρC σ := by
  have hfS : ∀ x ∈ p.range, cycSubOne ρC σ x ∈ p.range := by
    rintro _ ⟨b, rfl⟩
    exact ⟨cycSubOne ρB σ b, by rw [cycSubOne_apply, cycSubOne_apply, map_sub, hpG]⟩
  have hgS : ∀ x ∈ p.range, cycNorm ρC x ∈ p.range := by
    rintro _ ⟨b, rfl⟩
    exact ⟨cycNorm ρB b, by rw [cycNorm_apply, cycNorm_apply, map_sum]; simp only [hpG]⟩
  have : p.range.FiniteIndex := AddSubgroup.finiteIndex_of_finite_quotient
  have hR := (hasHerbrandQuotient_restrictEnd_iff p.range hfS hgS (cycSubOne_cycNorm ρC σ)
    (cycNorm_cycSubOne ρC σ)).2 hC
  have hex' : Function.Exact i p.rangeRestrict := by
    intro b
    rw [← hex b]
    constructor
    · intro h
      simpa using congrArg Subtype.val h
    · intro h
      exact Subtype.ext (by simpa using h)
  rw [cycHerbrand, cycHerbrand, cycHerbrand, ← herbrandQuotient_restrictEnd p.range hfS hgS
    (cycSubOne_cycNorm ρC σ) (cycNorm_cycSubOne ρC σ)]
  exact herbrandQuotient_eq_mul_of_shortExact hi p.rangeRestrict_surjective hex'
    (fun a => by rw [cycSubOne_apply, cycSubOne_apply, map_sub, hiG])
    (fun a => by rw [cycNorm_apply, cycNorm_apply, map_sum]; simp only [hiG])
    (fun b => Subtype.ext (by
      change p (cycSubOne ρB σ b) = cycSubOne ρC σ (p b)
      rw [cycSubOne_apply, cycSubOne_apply, map_sub, hpG]))
    (fun b => Subtype.ext (by
      change p (cycNorm ρB b) = cycNorm ρC (p b)
      rw [cycNorm_apply, cycNorm_apply, map_sum]; simp only [hpG]))
    (cycSubOne_cycNorm ρB σ) (cycNorm_cycSubOne ρB σ) hA hR

theorem cycHerbrand_eq_of_surjective_of_finite_ker (ρB : Representation ℤ G B)
    (ρC : Representation ℤ G C) (σ : G) {p : B →+ C} (hp : Function.Surjective p)
    [Finite p.ker] (hpG : ∀ g b, p (ρB g b) = ρC g (p b))
    (hC : HasHerbrandQuotient (cycSubOne ρC σ) (cycNorm ρC)) :
    cycHerbrand ρB σ = cycHerbrand ρC σ := by
  have hfK : ∀ x ∈ p.ker, cycSubOne ρB σ x ∈ p.ker := by
    intro x hx
    rw [AddMonoidHom.mem_ker] at hx ⊢
    rw [cycSubOne_apply, map_sub, hpG, hx, map_zero, sub_zero]
  have hgK : ∀ x ∈ p.ker, cycNorm ρB x ∈ p.ker := by
    intro x hx
    rw [AddMonoidHom.mem_ker] at hx ⊢
    set_option synthInstance.maxHeartbeats 100000 in
      rw [cycNorm_apply, map_sum]
    simp [hpG, hx]
  have hfgK : ∀ x, restrictEnd (cycSubOne ρB σ) p.ker hfK
      (restrictEnd (cycNorm ρB) p.ker hgK x) = 0 := fun x =>
    Subtype.ext (by
      change cycSubOne ρB σ (cycNorm ρB x.val) = 0
      exact cycSubOne_cycNorm ρB σ x.val)
  have hgfK : ∀ x, restrictEnd (cycNorm ρB) p.ker hgK
      (restrictEnd (cycSubOne ρB σ) p.ker hfK x) = 0 := fun x =>
    Subtype.ext (by
      change cycNorm ρB (cycSubOne ρB σ x.val) = 0
      exact cycNorm_cycSubOne ρB σ x.val)
  have hA : HasHerbrandQuotient (restrictEnd (cycSubOne ρB σ) p.ker hfK)
      (restrictEnd (cycNorm ρB) p.ker hgK) := hasHerbrandQuotient_of_finite _ _
  have hex : Function.Exact p.ker.subtype p := by
    intro b
    simp
  set_option synthInstance.maxHeartbeats 100000 in
    rw [cycHerbrand, cycHerbrand,
    herbrandQuotient_eq_mul_of_shortExact p.ker.subtype_injective hp hex
      (fun _ => rfl) (fun _ => rfl)
      (fun b => by rw [cycSubOne_apply, cycSubOne_apply, map_sub, hpG])
      (fun b => by rw [cycNorm_apply, cycNorm_apply, map_sum]; simp only [hpG])
      (cycSubOne_cycNorm ρB σ) (cycNorm_cycSubOne ρB σ) hA hC,
    herbrandQuotient_eq_one_of_finite hfgK hgfK, one_mul]

theorem cycHerbrand_prod (ρA : Representation ℤ G A) (ρB : Representation ℤ G B) (σ : G)
    (hA : HasHerbrandQuotient (cycSubOne ρA σ) (cycNorm ρA))
    (hB : HasHerbrandQuotient (cycSubOne ρB σ) (cycNorm ρB)) :
    cycHerbrand (ρA.prod ρB) σ = cycHerbrand ρA σ * cycHerbrand ρB σ := by
  have : Finite (B ⧸ (AddMonoidHom.snd A B).range) := by
    rw [AddMonoidHom.range_eq_top.2 (fun b => ⟨(0, b), rfl⟩)]
    infer_instance
  refine cycHerbrand_eq_mul_of_exact ρA (ρA.prod ρB) ρB σ (i := AddMonoidHom.inl A B)
    (p := AddMonoidHom.snd A B) (fun a a' h => congrArg Prod.fst h) ?_ (fun g a => ?_)
    (fun g b => rfl) hA hB
  · rintro ⟨a, b⟩
    simp only [AddMonoidHom.coe_snd, Set.mem_range, AddMonoidHom.inl_apply, Prod.ext_iff]
    constructor
    · rintro rfl
      exact ⟨a, rfl, rfl⟩
    · rintro ⟨a', -, rfl⟩
      rfl
  · exact Prod.ext rfl (map_zero (ρB g)).symm

end GroundTheory.Global
