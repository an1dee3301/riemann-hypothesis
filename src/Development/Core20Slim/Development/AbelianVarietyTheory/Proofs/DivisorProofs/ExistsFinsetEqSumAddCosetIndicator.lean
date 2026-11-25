module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.AddCharNegEqOne
public import Init.BinderNameHint
public import Init.Classical
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.PropLemmas
public import Init.SimpLemmas
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Quotient
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Quot
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.GroupTheory.Coset.Defs
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.Order.SetNotation
public import Mathlib.Tactic.Push
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Support
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Topology.Neighborhoods

@[expose] public section

open Filter Topology

namespace GlobalTheory.LinSchur


open Classical in
theorem exists_finset_eq_sum_cind {X : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
    (L : AddSubgroup X) (hL : IsOpen (L : Set X)) (f : X → ℂ) (hf : f ∈ GlobalTheory.WeilM.SB X)
    (hper : ∀ Y, ∀ C ∈ L, f (Y + C) = f Y) :
    ∃ F : Finset X, f = ∑ y ∈ F, f y • GlobalTheory.LinSchur.cind L y := by
  have hK : IsCompact (tsupport f) := hf.2
  obtain ⟨F0, -, hcov⟩ := hK.elim_nhds_subcover (fun x => {Y | Y - x ∈ L}) (fun x _ =>
    (hL.preimage (continuous_id.sub continuous_const)).mem_nhds (by simp))
  refine ⟨(F0.image (QuotientAddGroup.mk (s := L))).image Quotient.out, ?_⟩
  have hmk : ∀ y ∈ (F0.image (QuotientAddGroup.mk (s := L))).image Quotient.out, ∀ Y : X,
      Y - y ∈ L ↔ (QuotientAddGroup.mk Y : X ⧸ L) = QuotientAddGroup.mk y := by
    intro y _ Y
    rw [QuotientAddGroup.eq, ← neg_mem_iff]
    simp [sub_eq_add_neg, add_comm]
  funext Y
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, GlobalTheory.LinSchur.cind]
  by_cases hex : ∃ y ∈ (F0.image (QuotientAddGroup.mk (s := L))).image Quotient.out, Y - y ∈ L
  · obtain ⟨y, hy, hYy⟩ := hex
    rw [Finset.sum_eq_single y]
    · rw [if_pos hYy, mul_one]
      have := hper y (Y - y) hYy
      rw [add_sub_cancel] at this
      exact this
    · intro y' hy' hne
      rw [if_neg, mul_zero]
      intro hY'
      apply hne
      obtain ⟨q', -, rfl⟩ := Finset.mem_image.mp hy'
      obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp hy
      have e1 := (hmk _ hy' Y).mp hY'
      have e2 := (hmk _ hy Y).mp hYy
      simp only [QuotientAddGroup.out_eq'] at e1 e2
      rw [← e1, ← e2]
    · intro h; exact absurd hy h
  · push_neg at hex
    rw [Finset.sum_eq_zero (fun y hy => by rw [if_neg (hex y hy), mul_zero])]
    apply image_eq_zero_of_notMem_tsupport
    intro hY
    have := hcov hY
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop] at this
    obtain ⟨y0, hy0, hYy0⟩ := this
    have hmem : (QuotientAddGroup.mk y0 : X ⧸ L).out ∈
        (F0.image (QuotientAddGroup.mk (s := L))).image Quotient.out :=
      Finset.mem_image.mpr ⟨_, Finset.mem_image.mpr ⟨y0, hy0, rfl⟩, rfl⟩
    apply hex _ hmem
    rw [hmk _ hmem, QuotientAddGroup.out_eq']
    rw [← QuotientAddGroup.eq_iff_sub_mem.mpr hYy0]

end GlobalTheory.LinSchur
