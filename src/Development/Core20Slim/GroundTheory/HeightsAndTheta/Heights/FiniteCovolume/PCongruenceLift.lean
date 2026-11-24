module

public import Mathlib
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsStabilizerLevi
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PComplementLattice
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PComplementExtension
public import Development.Core20Slim.Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsNsmulMem
public import Development.Core20Slim.GroundTheory.AutomorphicForms.HermitianSpaces
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.MajorantInvolutionDiagonalForm
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Objects
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsComplementForm
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Basic
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.End
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.Hom.Basic
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Subgroup
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.LinearMap
public import Mathlib.Algebra.Module.Torsion.Free
public import Mathlib.Algebra.NoZeroSMulDivisors.Basic
public import Mathlib.Algebra.NoZeroSMulDivisors.Defs
public import Mathlib.Algebra.Quotient
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Basic.Finite.Prod
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Int.Cast.Lemmas
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.GroupTheory.Coset.Defs
public import Mathlib.GroupTheory.FiniteAbelian.Basic
public import Mathlib.GroupTheory.Finiteness
public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module
open scoped Pointwise

noncomputable section

namespace CongruenceLift

theorem exists_nsmul_mem {E W : Type*} [Field E] [NumberField E] [AddCommGroup W] [Module E W]
    {La : AddSubgroup W} (hLa : IsLattice E La) (w : W) : ∃ d : ℕ, 0 < d ∧ d • w ∈ La :=
  _root_.UpperTheory.Reformulated.B.ExistsNsmulMem.exists_nsmul_mem hLa w

theorem exists_congruence {V G : Type*} [AddCommGroup V] [Group G] [DistribMulAction G V]
    (L : AddSubgroup V) (hL : L.FG) (d : ℕ) (hd : 0 < d) :
    ∃ K : Subgroup (MulAction.stabilizer G L), K.index ≠ 0 ∧
      ∀ k ∈ K, ∀ y ∈ L, ∃ u ∈ L, d • u = (k : G) • y - y := by
  set S := MulAction.stabilizer G L
  have hS : ∀ (s : S) (y : V), y ∈ L → (s : G) • y ∈ L := fun s y hy => by
    have := AddSubgroup.smul_mem_pointwise_smul y (s : G) L hy
    rwa [MulAction.mem_stabilizer_iff.1 s.2] at this
  let f : S → L →+ L := fun s =>
    { toFun := fun y => ⟨(s : G) • (y : V), hS s y y.2⟩
      map_zero' := Subtype.ext (smul_zero _)
      map_add' := fun y z => Subtype.ext (smul_add _ _ _) }
  set N : AddSubgroup L := (nsmulAddMonoidHom (α := L) d).range
  have hN : ∀ s, N ≤ N.comap (f s) := by
    rintro s _ ⟨u, rfl⟩
    exact ⟨f s u, by simp [map_nsmul]⟩
  let _ : MulAction S (L ⧸ N) :=
    { smul := fun s q => QuotientAddGroup.map N N (f s) (hN s) q
      one_smul := fun q => QuotientAddGroup.induction_on q fun y => by
        change QuotientAddGroup.map N N (f 1) (hN 1) (y : L ⧸ N) = y
        rw [QuotientAddGroup.map_mk]
        congr 1
        exact Subtype.ext (one_smul G (y : V))
      mul_smul := fun s t q => QuotientAddGroup.induction_on q fun y => by
        change QuotientAddGroup.map N N (f (s * t)) (hN _) (y : L ⧸ N) =
          QuotientAddGroup.map N N (f s) (hN s) (QuotientAddGroup.map N N (f t) (hN t) y)
        rw [QuotientAddGroup.map_mk, QuotientAddGroup.map_mk, QuotientAddGroup.map_mk]
        congr 1
        exact Subtype.ext (mul_smul (s : G) (t : G) (y : V)) }
  have hfg : AddGroup.FG L := (AddGroup.fg_iff_addSubgroup_fg L).2 hL
  have hfin : Finite (L ⧸ N) := by
    refine AddCommGroup.finite_of_fg_isAddTorsion _ fun q => ?_
    refine QuotientAddGroup.induction_on q fun y => ?_
    rw [isOfFinAddOrder_iff_nsmul_eq_zero]
    refine ⟨d, hd, ?_⟩
    rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff]
    exact ⟨y, rfl⟩
  refine ⟨(MulAction.toPermHom S (L ⧸ N)).ker, Subgroup.FiniteIndex.index_ne_zero, ?_⟩
  intro k hk y hy
  have hq := DFunLike.congr_fun (MonoidHom.mem_ker.1 hk) ((⟨y, hy⟩ : L) : L ⧸ N)
  simp only [MulAction.toPermHom_apply, MulAction.toPerm_apply, Equiv.Perm.coe_one, id_eq] at hq
  change QuotientAddGroup.map N N (f k) (hN k) _ = _ at hq
  rw [QuotientAddGroup.map_mk, QuotientAddGroup.eq] at hq
  obtain ⟨u, hu⟩ := hq
  refine ⟨-(u : V), L.neg_mem u.2, ?_⟩
  have := congrArg Subtype.val hu
  simp only [nsmulAddMonoidHom_apply, AddSubgroup.coe_nsmul, AddSubgroup.coe_add,
    AddSubgroup.coe_neg] at this
  rw [smul_neg, this]
  change -(-((k : G) • y) + y) = (k : G) • y - y
  abel

end CongruenceLift

variable {F E : Type*} [Field F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W]

theorem CongruenceLift.proof [FiniteDimensional E W] (h : HermitianForm F E W) :
    CongruenceLift.Statement h := by
  intro D La x₀ w₀ hLa hx₀ hp h' hh'
  obtain ⟨d, hd, hdw⟩ := CongruenceLift.exists_nsmul_mem hLa.isLattice w₀
  set La' : AddSubgroup (hypComplement h x₀ w₀) := La.comap (hypComplement h x₀ w₀).subtype.toAddMonoidHom
  have dec : ∀ x ∈ La, h.toSesq (d • w₀) x • x₀ ∈ La ∧ (h.toSesq x₀ x * d) • w₀ ∈ La ∧
      d • x - h.toSesq (d • w₀) x • x₀ - (h.toSesq x₀ x * d) • w₀ =
        ((d • ComplementExtension.proj hp x : hypComplement h x₀ w₀) : W) := by
    intro x hx
    refine ⟨hLa.isLattice.smul_mem ⟨_, hLa.integral _ hdw x hx⟩ x₀ hx₀, ?_, ?_⟩
    · have := hLa.isLattice.smul_mem ⟨_, hLa.integral _ hx₀ x hx⟩ _ hdw
      rwa [← Nat.cast_smul_eq_nsmul E, smul_smul] at this
    · rw [Submodule.coe_smul_of_tower, ComplementExtension.proj_apply, map_nsmul,
        LinearMap.smul_apply]
      simp only [← Nat.cast_smul_eq_nsmul E, smul_eq_mul]
      module
  obtain ⟨D', hD'⟩ := ComplementLattice.proof h x₀ w₀ hp h' hh' D d hd
  have hLa' : IsDIntegral h' D' La' := hD' La hLa fun x hx =>
    ⟨_, (dec x hx).1, _, (dec x hx).2.1, by rw [(dec x hx).2.2]; exact Submodule.coe_mem _⟩
  obtain ⟨K, hK, hcong⟩ : ∃ K : Subgroup (latticeStab h' La'), K.index ≠ 0 ∧
      ∀ k ∈ K, ∀ y ∈ La', ∃ u ∈ La', d • u = (k : h'.unitaryGroup) • y - y :=
    CongruenceLift.exists_congruence (G := h'.unitaryGroup) La' hLa'.isLattice.fg d hd
  have key : ∀ k ∈ K, ∀ γ : h.unitaryGroup, γ • x₀ = x₀ → γ • w₀ = w₀ →
      (∀ x : hypComplement h x₀ w₀, γ • (x : W) = ((((k : latticeStab h' La') : h'.unitaryGroup) • x : hypComplement h x₀ w₀) : W)) →
      ∀ x ∈ La, γ • x ∈ La := by
    intro k hk γ h1 h2 h3 x hx
    obtain ⟨hA, hB, hC⟩ := dec x hx
    set y : hypComplement h x₀ w₀ := d • ComplementExtension.proj hp x
    have hy : y ∈ La' := by
      change (y : W) ∈ La
      rw [← hC]
      exact La.sub_mem (La.sub_mem (La.nsmul_mem hx d) hA) hB
    obtain ⟨u, hu, hdu⟩ := hcong k hk y hy
    have hx' : d • x = h.toSesq (d • w₀) x • x₀ + (y : W) + (h.toSesq x₀ x * d) • w₀ := by
      rw [← hC]
      abel
    have hγ : d • (γ • x) = d • (x + (u : W)) := by
      have hdu' : (((k : latticeStab h' La') : h'.unitaryGroup) • y : hypComplement h x₀ w₀) = (y : W) + d • (u : W) := by
        rw [← Submodule.coe_smul_of_tower, hdu]
        simp
      rw [← smul_comm, hx', smul_add, smul_add, smul_comm γ (h.toSesq (d • w₀) x),
        smul_comm γ (h.toSesq x₀ x * d), h1, h2, h3, hdu', smul_add, hx']
      abel
    have hne : (d : E) ≠ 0 := Nat.cast_ne_zero.2 hd.ne'
    have := smul_right_injective W hne (by simpa only [Nat.cast_smul_eq_nsmul] using hγ)
    rw [this]
    exact La.add_mem hx hu
  refine ⟨D', La', K.map (latticeStab h' La').subtype, hLa', Subgroup.map_subtype_le K, ?_, ?_⟩
  · rw [Subgroup.relIndex, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective (latticeStab h' La').subtype_injective]
    exact hK
  · rintro _ ⟨k, hk, rfl⟩ γ h1 h2 h3
    refine MulAction.mem_stabilizer_iff.2 (le_antisymm ?_ ?_)
    · intro z hz
      obtain ⟨x, hx, rfl⟩ := (AddSubgroup.mem_smul_pointwise_iff_exists z γ La).1 hz
      exact key k hk γ h1 h2 h3 x hx
    · intro z hz
      refine AddSubgroup.mem_pointwise_smul_iff_inv_smul_mem.2 ?_
      refine key k⁻¹ (K.inv_mem hk) γ⁻¹ (inv_smul_eq_iff.2 h1.symm) (inv_smul_eq_iff.2 h2.symm)
        (fun x => inv_smul_eq_iff.2 ?_) z hz
      rw [h3]
      simp

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
