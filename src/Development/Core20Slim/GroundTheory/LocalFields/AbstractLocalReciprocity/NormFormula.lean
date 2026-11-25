module

public import Mathlib
public import Development.Core20Slim.GroundTheory.LocalFields.AbstractLocalReciprocity.UniqueQuotientSubgroupOfSelf
public import Development.Core20Slim.GroundTheory.LocalFields.AbstractLocalReciprocity.ExistsOpenSubgroupMemFixedModule
public import Init.Core
public import Init.Data.Function
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Quotient
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Basic.Unique
public import Mathlib.Data.Quot
public import Mathlib.GroupTheory.Coset.Defs
public import Mathlib.GroupTheory.Index
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Logic.Function.Defs
public import Mathlib.Order.Defs.PartialOrder

set_option synthInstance.maxHeartbeats 400000

@[expose] public section

namespace GroundTheory.LocalField.Abstract

variable {G : Type*} [Group G] {A : Type*} [CommGroup A] [MulDistribMulAction G A]

theorem coe_norm_of_le {K L : Subgroup G} (hKL : K ≤ L) [(L.subgroupOf K).FiniteIndex]
    (a : fixedModule A L) : (norm A K L a : A) = a := by
  have : Unique (K ⧸ L.subgroupOf K) :=
    { default := ((1 : K) : K ⧸ L.subgroupOf K)
      uniq := fun q => by
        induction q using QuotientGroup.induction_on with
        | H σ =>
          rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
          exact hKL (by simp) }
  rw [coe_norm, finprod_eq_single _ ((1 : K) : K ⧸ L.subgroupOf K)
    (fun q hq => absurd (Subsingleton.elim q _) hq), cosetSMul_mk]
  simp

theorem coe_norm_congr {K K' L L' : Subgroup G} (hK : K = K') (hL : L = L')
    [(L.subgroupOf K).FiniteIndex] [(L'.subgroupOf K').FiniteIndex] (a : fixedModule A L) :
    (norm A K L a : A) = norm A K' L' ⟨a, hL ▸ a.2⟩ := by
  subst hK
  subst hL
  rfl

theorem smul_norm_of_map_eq {K L : Subgroup G} (g : G) (hK : K.map (MulAut.conj g).toMonoidHom = K)
    (hL : L.map (MulAut.conj g).toMonoidHom = L) [(L.subgroupOf K).FiniteIndex]
    (a : fixedModule A L) :
    g • (norm A K L a : A) = norm A K L ⟨g • (a : A), by
      have := smul_mem_fixedModule a.2 g
      rwa [hL] at this⟩ := by
  have : ((L.map (MulAut.conj g).toMonoidHom).subgroupOf
      (K.map (MulAut.conj g).toMonoidHom)).FiniteIndex := by
    rw [hK, hL]
    infer_instance
  rw [smul_norm g a, coe_norm_congr hK hL]

theorem coe_norm_eq_of_mul_eq {K S Q J : Subgroup G} (hQK : Q ≤ K)
    (hmul : ∀ k ∈ K, ∃ q ∈ Q, q⁻¹ * k ∈ S) (hJ : ∀ q ∈ Q, q ∈ S ↔ q ∈ J)
    [(S.subgroupOf K).FiniteIndex] [(J.subgroupOf Q).FiniteIndex] (a : fixedModule A S)
    (ha : (a : A) ∈ fixedModule A J) :
    (norm A K S a : A) = norm A Q J ⟨a, ha⟩ := by
  let f : Q ⧸ J.subgroupOf Q → K ⧸ S.subgroupOf K :=
    Quotient.map' (fun q : Q => (⟨q, hQK q.2⟩ : K)) fun q q' h => by
      rw [QuotientGroup.leftRel_apply, Subgroup.mem_subgroupOf] at h ⊢
      have hq : ((q⁻¹ * q' : Q) : G) ∈ Q := (q⁻¹ * q').2
      simpa using (hJ _ hq).2 h
  have hf : Function.Bijective f := by
    constructor
    · intro x y hxy
      induction x using QuotientGroup.induction_on with
      | H q =>
      induction y using QuotientGroup.induction_on with
      | H q' =>
        have h' : ((⟨q, hQK q.2⟩ : K) : K ⧸ S.subgroupOf K) = ((⟨q', hQK q'.2⟩ : K) : K ⧸ _) := hxy
        rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at h'
        rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
        have hq : ((q⁻¹ * q' : Q) : G) ∈ Q := (q⁻¹ * q').2
        exact (hJ _ hq).1 (by simpa using h')
    · intro y
      induction y using QuotientGroup.induction_on with
      | H k =>
        obtain ⟨q, hq, hqk⟩ := hmul k k.2
        refine ⟨((⟨q, hq⟩ : Q) : Q ⧸ J.subgroupOf Q), ?_⟩
        show ((⟨q, hQK hq⟩ : K) : K ⧸ S.subgroupOf K) = _
        rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
        simpa using hqk
  rw [coe_norm, coe_norm, ← finprod_comp_equiv (Equiv.ofBijective f hf)]
  congr 1
  funext x
  induction x using QuotientGroup.induction_on with
  | H q => rfl

end GroundTheory.LocalField.Abstract
