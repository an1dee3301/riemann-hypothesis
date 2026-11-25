module

public import Mathlib
public import Development.Core20Slim.GroundTheory.LocalFields.AbstractLocalReciprocity.NormFormula
public import Development.Core20Slim.GroundTheory.LocalFields.AbstractLocalReciprocity.Reciprocity
public import Development.Core20Slim.GroundTheory.LocalFields.AbstractLocalReciprocity.ExistsEqNsmulOfProjEqZero
public import Development.Core20Slim.GroundTheory.LocalFields.AbstractLocalReciprocity.ExistsOpenSubgroupMemFixedModule
public import Development.Core20Slim.GroundTheory.LocalFields.AbstractLocalReciprocity.Frobenius
public import Development.Core20Slim.GroundTheory.LocalFields.AbstractLocalReciprocity.ProfiniteInteger
public import Development.Core20Slim.GroundTheory.LocalFields.AbstractLocalReciprocity.Valuation
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Fin.Lemmas
public import Init.Data.Function
public import Init.Data.Int.Basic
public import Init.Data.Int.DivMod.Basic
public import Init.Data.Int.Lemmas
public import Init.Data.Int.Order
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Ext
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Prelude
public import Init.SimpLemmas
public import Init.SizeOf
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.GroupWithZero.Action
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Divisibility.Basic
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Divisibility
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.Group.Abs
public import Mathlib.Algebra.Order.Group.Int
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.Group.Unbundled.Int
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Algebra.Quotient
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Pi
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Int.Cast.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Int.Cast.Lemmas
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.PNat.Defs
public import Mathlib.Data.PNat.Notation
public import Mathlib.Data.Quot
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.ZMod.Defs
public import Mathlib.GroupTheory.Coset.Defs
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.Index
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Logic.Function.Defs
public import Mathlib.Order.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Defs
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Hom.Basic
public import Mathlib.Order.Lattice
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.Topology.Connected.TotallyDisconnected
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter

set_option synthInstance.maxHeartbeats 400000

@[expose] public section

namespace GroundTheory.LocalField.Abstract

open ProfiniteInteger

variable {G : Type*} [Group G] {A : Type*} [CommGroup A] [MulDistribMulAction G A]

theorem coe_norm_eq_prod_smul_norm (d : G →* Multiplicative ℤ̂) {K S J : Subgroup G} {f n : ℕ}
    (hn : 0 < n) (hf : 0 < f) (hSK : S ≤ K)
    (hdS : ∀ s ∈ S, Multiplicative.toAdd (d s) ∈ multiples (n * f))
    (hsurj : ∀ k ∈ K, Multiplicative.toAdd (d k) ∈ multiples (n * f) → ∃ s ∈ S, d s = d k)
    (hdK : ∀ k ∈ K, Multiplicative.toAdd (d k) ∈ multiples f)
    (hJ : ∀ q ∈ K ⊓ d.ker, q ∈ S ↔ q ∈ J)
    {φ : G} (hφK : φ ∈ K) (hdφ : d φ = Multiplicative.ofAdd (f : ℤ̂))
    [(S.subgroupOf K).FiniteIndex] [(J.subgroupOf (K ⊓ d.ker)).FiniteIndex]
    (a : fixedModule A S) (ha : (a : A) ∈ fixedModule A J) :
    (norm A K S a : A) =
      ∏ ν : Fin n, φ ^ (ν : ℕ) • (norm A (K ⊓ d.ker) J ⟨a, ha⟩ : A) := by
  classical
  set Q := K ⊓ d.ker with hQ
  have hQK : Q ≤ K := inf_le_left

  let incl : Q ⧸ J.subgroupOf Q → K ⧸ S.subgroupOf K :=
    Quotient.map' (fun q : Q => (⟨q, hQK q.2⟩ : K)) fun q q' h => by
      rw [QuotientGroup.leftRel_apply, Subgroup.mem_subgroupOf] at h ⊢
      have hq : ((q⁻¹ * q' : Q) : G) ∈ Q := (q⁻¹ * q').2
      simpa using (hJ _ hq).2 h
  let φK : K := ⟨φ, hφK⟩
  let F : Fin n × (Q ⧸ J.subgroupOf Q) → K ⧸ S.subgroupOf K := fun p => (φK ^ (p.1 : ℕ)) • incl p.2
  have hFmk : ∀ (ν : Fin n) (q : Q), F (ν, (q : Q ⧸ J.subgroupOf Q)) =
      ((φK ^ (ν : ℕ) * ⟨q, hQK q.2⟩ : K) : K ⧸ S.subgroupOf K) := fun _ _ => rfl

  have hdeg : ∀ (m : ℤ) (q : G), q ∈ Q →
      Multiplicative.toAdd (d (φ ^ m * q)) = ((m * f : ℤ) : ℤ̂) := by
    intro m q hq
    rw [map_mul, map_zpow, hdφ, (MonoidHom.mem_ker).1 hq.2, mul_one, ← ofAdd_zsmul, toAdd_ofAdd,
      zsmul_eq_mul]
    push_cast
    ring
  have hF : Function.Bijective F := by
    constructor
    · rintro ⟨ν, x⟩ ⟨μ, y⟩ hxy
      induction x using QuotientGroup.induction_on with
      | H q =>
      induction y using QuotientGroup.induction_on with
      | H q' =>
        rw [hFmk, hFmk, QuotientGroup.eq, Subgroup.mem_subgroupOf] at hxy
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, SubmonoidClass.coe_pow] at hxy

        have hx : ((φ ^ (ν : ℕ) * (q : G))⁻¹ * (φ ^ (μ : ℕ) * q') : G) =
            (q : G)⁻¹ * (φ ^ ((μ : ℤ) - ν) * q') := by
          rw [zpow_sub, zpow_natCast, zpow_natCast]
          group
        have hdq : Multiplicative.toAdd (d ((q : G)⁻¹ * (φ ^ ((μ : ℤ) - ν) * q'))) =
            ((((μ : ℤ) - ν) * f : ℤ) : ℤ̂) := by
          rw [map_mul, map_inv, (MonoidHom.mem_ker).1 q.2.2, inv_one, one_mul]
          exact hdeg _ _ q'.2
        have hmem := hdS _ hxy
        rw [hx, hdq] at hmem
        have hdvd := (intCast_mem_multiples_iff (Nat.mul_pos hn hf)).1 hmem
        push_cast at hdvd
        have hdvd' : (n : ℤ) ∣ (μ : ℤ) - ν :=
          (mul_dvd_mul_iff_right (by exact_mod_cast hf.ne')).1 hdvd
        have hνμ : ν = μ := by
          have hμ := μ.2
          have hν := ν.2
          have h0 : ((μ : ℤ) - ν) = 0 :=
            Int.eq_zero_of_abs_lt_dvd hdvd' (abs_sub_lt_iff.2 ⟨by omega, by omega⟩)
          exact Fin.ext (by omega)
        subst hνμ
        have hqq : (q : G)⁻¹ * q' ∈ S := by simpa [mul_assoc] using hxy
        have hqQ : (q : G)⁻¹ * q' ∈ Q := Q.mul_mem (Q.inv_mem q.2) q'.2
        refine Prod.ext rfl ?_
        rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
        simpa using (hJ _ hqQ).1 hqq
    · intro y
      induction y using QuotientGroup.induction_on with
      | H k =>
        obtain ⟨w, hw⟩ := mem_multiples.1 (hdK k k.2)
        set N : ℕ+ := ⟨n, hn⟩ with hNdef
        set ν : ℕ := (proj N w).val with hνdef
        have hνn : ν < n := ZMod.val_lt _
        have hw' : w - (ν : ℤ̂) ∈ multiples n := by
          have := (proj_eq_zero_iff (n := N) (x := w - (ν : ℤ̂))).1 (by
            rw [map_sub, map_natCast, hνdef, ZMod.natCast_zmod_val, sub_self])
          simpa [hNdef] using this
        obtain ⟨z, hz⟩ := mem_multiples.1 hw'
        have hdk : Multiplicative.toAdd (d (φ ^ (-(ν : ℤ)) * k)) ∈ multiples (n * f) := by
          rw [map_mul, map_zpow, hdφ, ← ofAdd_zsmul, toAdd_mul, toAdd_ofAdd, hw]
          refine mem_multiples.2 ⟨z, ?_⟩
          have : w = (ν : ℤ̂) + n • z := by rw [← hz]; ring
          rw [this]
          simp only [nsmul_eq_mul, zsmul_eq_mul]
          push_cast
          ring
        obtain ⟨s, hs, hds⟩ := hsurj _ (K.mul_mem (K.zpow_mem hφK _) k.2) hdk
        set q : G := φ ^ (-(ν : ℤ)) * k * s⁻¹ with hqdef
        have hqQ : q ∈ Q := by
          refine ⟨K.mul_mem (K.mul_mem (K.zpow_mem hφK _) k.2) (K.inv_mem (hSK hs)), ?_⟩
          show d q = 1
          rw [hqdef, map_mul, map_inv, ← hds, mul_inv_cancel]
        refine ⟨(⟨ν, hνn⟩, ((⟨q, hqQ⟩ : Q) : Q ⧸ J.subgroupOf Q)), ?_⟩
        rw [hFmk, QuotientGroup.eq, Subgroup.mem_subgroupOf]
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, SubmonoidClass.coe_pow, hqdef]
        have : ((φ ^ ν * (φ ^ (-(ν : ℤ)) * (k : G) * s⁻¹))⁻¹ * k : G) = s := by
          rw [zpow_neg, zpow_natCast]
          group
        rw [this]
        exact hs
  rw [coe_norm, ← finprod_comp_equiv (Equiv.ofBijective F hF)]
  let _ := Fintype.ofFinite (Q ⧸ J.subgroupOf Q)
  rw [finprod_eq_prod_of_fintype, Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun ν _ => ?_
  rw [coe_norm, finprod_eq_prod_of_fintype, Finset.smul_prod']
  refine Finset.prod_congr rfl fun x _ => ?_
  induction x using QuotientGroup.induction_on with
  | H q =>
    rw [Equiv.ofBijective_apply, hFmk, cosetSMul_mk, cosetSMul_mk, smul_smul]
    rfl

namespace ClassFieldData

variable [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]
  {D : ClassFieldData G A} {K L : OpenSubgroup G}


omit [TotallyDisconnectedSpace G] in
instance finiteIndex_inf_ker (d : G →* Multiplicative ℤ̂) (K L : OpenSubgroup G) :
    (((L : Subgroup G) ⊓ d.ker).subgroupOf ((K : Subgroup G) ⊓ d.ker)).FiniteIndex := by
  have h : ((L : Subgroup G) ⊓ d.ker).subgroupOf ((K : Subgroup G) ⊓ d.ker) =
      (L : Subgroup G).subgroupOf ((K : Subgroup G) ⊓ d.ker) := by
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, and_iff_left_iff_imp]
    exact fun _ => x.2.2
  rw [h]
  infer_instance


omit [TotallyDisconnectedSpace G] in
theorem toAdd_deg_mem_multiples (K : OpenSubgroup G) {k : G} (hk : k ∈ (K : Subgroup G)) :
    Multiplicative.toAdd (D.deg k) ∈ multiples (inertiaDegree D.deg K) := by
  obtain ⟨y, hy⟩ := (D.mem_map_deg_iff K).1 ⟨k, hk, rfl⟩
  refine mem_multiples.2 ⟨Multiplicative.toAdd y, ?_⟩
  rw [← hy, toAdd_pow]

variable (hLK : L ≤ K) [((L : Subgroup G).subgroupOf K).Normal] (s : D.FrobeniusLift K)

theorem coe_norm_field_eq {φ : G} (hφK : φ ∈ (K : Subgroup G))
    (hdφ : D.deg φ = Multiplicative.ofAdd (inertiaDegree D.deg K : ℤ̂))
    (a : fixedModule A ((s.field L hLK : OpenSubgroup G) : Subgroup G)) :
    (norm A (K : Subgroup G) (s.field L hLK : Subgroup G) a : A) =
      ∏ ν : Fin s.deg, φ ^ (ν : ℕ) •
        (norm A ((K : Subgroup G) ⊓ D.deg.ker) ((L : Subgroup G) ⊓ D.deg.ker)
          ⟨a, fixedModule_anti le_frobeniusClosure a.2⟩ : A) := by
  have hnormalizer := FrobeniusLift.mem_normalizer (D := D) hLK s.mem
  have hmap := map_frobeniusClosure D.continuous_deg hnormalizer s.deg_eq (L := (L : Subgroup G))
  have hfield_le : (s.field L hLK : Subgroup G) ≤ (K : Subgroup G) :=
    frobeniusClosure_le K.isClosed s.mem (inf_le_left.trans hLK)
  have hfield_inf_ker :
      (s.field L hLK : Subgroup G) ⊓ D.deg.ker = (L : Subgroup G) ⊓ D.deg.ker :=
    frobeniusClosure_inf_ker D.continuous_deg L.isOpen hnormalizer
      (mul_ne_zero s.deg_pos.ne' (D.inertiaDegree_ne_zero K)) s.deg_eq
  refine coe_norm_eq_prod_smul_norm D.deg s.deg_pos (Nat.pos_of_ne_zero (D.inertiaDegree_ne_zero K))
    hfield_le ?_ ?_ (fun k hk => toAdd_deg_mem_multiples K hk) ?_ hφK hdφ a _
  · intro x hx
    have : D.deg x ∈ (frobeniusClosure D.deg L s.elt).map D.deg := ⟨x, hx, rfl⟩
    rw [hmap] at this
    exact this
  · intro k _ hk
    have : D.deg k ∈ AddSubgroup.toSubgroup (multiples (s.deg * inertiaDegree D.deg K)) := hk
    rw [← hmap] at this
    obtain ⟨x, hx, hxk⟩ := this
    exact ⟨x, hx, hxk⟩
  · intro q hq
    constructor
    · intro hqS
      exact hfield_inf_ker.le ⟨hqS, hq.2⟩
    · intro hqJ
      exact le_frobeniusClosure hqJ

end ClassFieldData

end GroundTheory.LocalField.Abstract
