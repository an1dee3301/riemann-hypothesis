module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedSpaceVecPairAsAdeles
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Init.BinderNameHint
public import Init.Classical
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Ext
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Indicator
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Algebra.Quotient
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Quot
public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Lattice.Indexed
public import Mathlib.Data.Set.Operations
public import Mathlib.GroupTheory.Coset.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Notation
public import Mathlib.Order.SetNotation
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Push
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.Group.ContinuousDiv
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Support
public import Mathlib.Topology.Clopen
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Topology.Neighborhoods

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix ENNReal Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.WeilAdm

theorem eq_sum_pureA_coset_indicator : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (U : AddSubgroup (κ → FiniteAdeleRing (𝓞 F) F))
    (K : Set (κ → FiniteAdeleRing (𝓞 F) F)), IsOpen (U : Set (κ → FiniteAdeleRing (𝓞 F) F)) → IsCompact (U : Set (κ → FiniteAdeleRing (𝓞 F) F)) → IsCompact K →
      ∃ R : Finset (κ → FiniteAdeleRing (𝓞 F) F),
        (∀ r ∈ R, Set.indicator {y | y - r ∈ U} (fun _ => (1 : ℂ)) ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F)) ∧
        ∀ Φ : (κ → AdeleRing (𝓞 F) F) → ℂ, (∀ x, ∀ u ∈ U, Φ (x + GlobalTheory.WeilAdm.finE F u) = Φ x) →
          (∀ x, (fun i => (x i).2) ∉ K → Φ x = 0) →
            Φ = ∑ r ∈ R, GlobalTheory.WeilM.pureA F (GlobalTheory.WeilAdm.slice F Φ r) (Set.indicator {y | y - r ∈ U} fun _ => (1 : ℂ)) := by
  intro F _ _ κ _ U K hUo hUc hK
  classical
  have hcov : K ⊆ ⋃ y : (κ → FiniteAdeleRing (𝓞 F) F), {x | x - y ∈ U} := by
    intro x _
    exact Set.mem_iUnion.2 ⟨x, by simp [U.zero_mem]⟩
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun y => {x | x - y ∈ U})
    (fun y => hUo.preimage (continuous_id.sub continuous_const)) hcov
  let R : Finset (κ → FiniteAdeleRing (𝓞 F) F) :=
    (t.image (QuotientAddGroup.mk : (κ → FiniteAdeleRing (𝓞 F) F) → _ ⧸ U)).image Quotient.out
  have hdist : ∀ r ∈ R, ∀ r' ∈ R, ∀ x, x - r ∈ U → x - r' ∈ U → r = r' := by
    intro r hr r' hr' x h h'
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hr
    obtain ⟨q', -, rfl⟩ := Finset.mem_image.1 hr'
    have e1 : (QuotientAddGroup.mk q.out : _ ⧸ U) = QuotientAddGroup.mk x :=
      QuotientAddGroup.eq.2 (by rwa [neg_add_eq_sub])
    have e2 : (QuotientAddGroup.mk q'.out : _ ⧸ U) = QuotientAddGroup.mk x :=
      QuotientAddGroup.eq.2 (by rwa [neg_add_eq_sub])
    rw [QuotientAddGroup.out_eq'] at e1 e2
    rw [e1, e2]
  have hcover : ∀ x ∈ K, ∃ r ∈ R, x - r ∈ U := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.1 (ht hx)
    refine ⟨(QuotientAddGroup.mk y : _ ⧸ U).out, Finset.mem_image_of_mem _ (Finset.mem_image_of_mem _ hy), ?_⟩
    have e : -(QuotientAddGroup.mk y : _ ⧸ U).out + y ∈ U :=
      QuotientAddGroup.eq.1 (QuotientAddGroup.out_eq' _)
    have := U.add_mem hxy e
    convert this using 1
    abel
  have hSB : ∀ r : κ → FiniteAdeleRing (𝓞 F) F,
      Set.indicator {y | y - r ∈ U} (fun _ => (1 : ℂ)) ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F) := by
    intro r
    have hcl : IsClopen {y : κ → FiniteAdeleRing (𝓞 F) F | y - r ∈ U} :=
      ⟨(AddSubgroup.isClosed_of_isOpen U hUo).preimage (continuous_id.sub continuous_const),
        hUo.preimage (continuous_id.sub continuous_const)⟩
    have hco : IsCompact {y : κ → FiniteAdeleRing (𝓞 F) F | y - r ∈ U} :=
      (Homeomorph.subRight r).isCompact_preimage.2 hUc
    refine ⟨?_, ?_⟩
    · rw [IsLocallyConstant.iff_eventually_eq]
      intro x
      by_cases hx : x ∈ {y : κ → FiniteAdeleRing (𝓞 F) F | y - r ∈ U}
      · filter_upwards [hcl.isOpen.mem_nhds hx] with y hy
        rw [Set.indicator_of_mem (show y ∈ {y : κ → FiniteAdeleRing (𝓞 F) F | y - r ∈ U} from hy),
          Set.indicator_of_mem hx]
      · filter_upwards [hcl.isClosed.isOpen_compl.mem_nhds hx] with y hy
        simp only [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]
    · exact HasCompactSupport.intro' hco hcl.isClosed (fun y hy => Set.indicator_of_notMem hy _)
  refine ⟨R, fun r _ => hSB r, fun Φ hinv hsupp => ?_⟩
  funext x
  rw [Finset.sum_apply]
  by_cases hx : ∃ r ∈ R, (fun i => (x i).2) - r ∈ U
  · obtain ⟨r0, hr0, hxr0⟩ := hx
    rw [Finset.sum_eq_single_of_mem r0 hr0]
    · have hm : (fun i => (x i).2) ∈ {y | y - r0 ∈ U} := hxr0
      simp only [GlobalTheory.WeilM.pureA, GlobalTheory.WeilAdm.slice, RingEquiv.symm_apply_apply, Set.indicator_of_mem hm, mul_one]
      obtain ⟨x', hx'⟩ : ∃ x' : κ → AdeleRing (𝓞 F) F, x' = fun i => ((x i).1, r0 i) := ⟨_, rfl⟩
      have e : x = x' + GlobalTheory.WeilAdm.finE F ((fun i => (x i).2) - r0) := by
        subst hx'
        funext i
        refine Prod.ext ?_ ?_
        · show (x i).1 = (x i).1 + 0
          rw [add_zero]
        · show (x i).2 = r0 i + ((x i).2 - r0 i)
          rw [add_sub_cancel]
      conv_lhs => rw [e]
      rw [hinv x' _ hxr0, hx']
    · intro r hr hne
      simp only [GlobalTheory.WeilM.pureA]
      have hm : (fun i => (x i).2) ∉ {y | y - r ∈ U} := fun h => hne (hdist r hr r0 hr0 _ h hxr0)
      rw [Set.indicator_of_notMem hm, mul_zero]
  · push_neg at hx
    have hK' : (fun i => (x i).2) ∉ K := fun h => by
      obtain ⟨r, hr, h'⟩ := hcover _ h
      exact hx r hr h'
    rw [hsupp x hK']
    symm
    apply Finset.sum_eq_zero
    intro r hr
    simp only [GlobalTheory.WeilM.pureA]
    have hm : (fun i => (x i).2) ∉ {y | y - r ∈ U} := hx r hr
    rw [Set.indicator_of_notMem hm, mul_zero]

end GlobalTheory.WeilAdm

end
