module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoMulInvOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DecayZero
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Classical
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Ext
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Basic
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.Algebra.Quotient
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.WithAbs
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Sets
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Prod.Basic
public import Mathlib.Data.Quot
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Lattice.Indexed
public import Mathlib.GroupTheory.Coset.Defs
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.Order.SetNotation
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Push
public import Mathlib.Topology.Algebra.Group.ContinuousInv
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Support
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.LocallyConstant.Basic

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SWQ GlobalTheory.ThetaTransform
open scoped Matrix Classical

noncomputable section

namespace GlobalTheory.LevelSchwartz

theorem mem_schA_of_level : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ) (Φ : (Fin N → AF F) → ℂ),
    (∃ U : AddSubgroup (Fin N → AF F), IsOpen (U : Set (Fin N → AF F)) ∧ ∀ u ∈ U, inf u = 0 → ∀ x, Φ (x + u) = Φ x) →
    (∃ K : Set (Fin N → Af F), IsCompact K ∧ ∀ x, Φ x ≠ 0 → fin x ∈ K) →
    (∀ x, ∃ g : SchwartzMap (Fin N → mixedEmbedding.mixedSpace F) ℂ, ∀ t, g t = Φ (x + embR t)) →
    Φ ∈ GlobalTheory.WeilM.schA F (Fin N) := by
  intro F _ _ N Φ ⟨U, hUo, hU⟩ ⟨K, hK, hKs⟩ hS
  let e := InfiniteAdeleRing.ringEquiv_mixedSpace F
  let ι : (Fin N → Af F) →+ (Fin N → AF F) :=
    { toFun := fun v i => pairA F 0 (v i)
      map_zero' := rfl
      map_add' := fun a b => by
        funext i
        show (((0 : Ainf F), a i + b i) : Ainf F × Af F) = ((0 : Ainf F), a i) + ((0 : Ainf F), b i)
        simp }
  have hιc : Continuous ι := continuous_pi fun i =>
    (show Continuous fun v : Fin N → Af F => (((0 : Ainf F), v i) : Ainf F × Af F) from
      continuous_const.prodMk (continuous_apply i))
  have hιinf : ∀ v, inf (ι v) = 0 := fun v => rfl
  have hfin : ∀ a t, fin (ι a + embR t) = a := fun a t => by
    funext i
    show (a i + 0 : Af F) = a i
    exact add_zero _
  have hdec : ∀ y : Fin N → AF F, y = ι (fin y) + embR (fun i => e (y i).1) := fun y => by
    funext i
    show (y i : Ainf F × Af F) = (((0 : Ainf F), (y i).2) : Ainf F × Af F) + ((e.symm (e (y i).1), (0 : Af F)))
    rw [RingEquiv.symm_apply_apply]
    refine Prod.ext ?_ ?_ <;> simp
  let W : AddSubgroup (Fin N → Af F) := U.comap ι
  have hWo : IsOpen (W : Set (Fin N → Af F)) := hUo.preimage hιc
  have hWcl : IsClosed (W : Set (Fin N → Af F)) := AddSubgroup.isClosed_of_isOpen W hWo
  have hinv : ∀ a b, -a + b ∈ W → ∀ z, Φ (ι b + z) = Φ (ι a + z) := by
    intro a b hab z
    rw [← hU (ι (-a + b)) hab (hιinf _) (ι a + z)]
    congr 1
    rw [map_add (f := _), map_neg]
    abel
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun a : Fin N → Af F => {b | -a + b ∈ W})
    (fun a => hWo.preimage (continuous_const.add continuous_id))
    (fun b _ => Set.mem_iUnion.2 ⟨b, show -b + b ∈ W by rw [neg_add_cancel]; exact W.zero_mem⟩)
  let T : Finset ((Fin N → Af F) ⧸ W) := t.image QuotientAddGroup.mk
  choose g hg using fun q : (Fin N → Af F) ⧸ W => hS (ι q.out)
  let ind : ((Fin N → Af F) ⧸ W) → (Fin N → Af F) → ℂ := fun q a =>
    if (QuotientAddGroup.mk a : (Fin N → Af F) ⧸ W) = q then 1 else 0
  have key : Φ = ∑ q ∈ T, GlobalTheory.WeilM.pureA F (g q) (ind q) := by
    funext y
    rw [Finset.sum_apply]
    show Φ y = ∑ q ∈ T, g q (fun i => e (y i).1) *
      (if (QuotientAddGroup.mk (fin y) : (Fin N → Af F) ⧸ W) = q then (1 : ℂ) else 0)
    simp only [mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq]
    split_ifs with hT
    · rw [hg]
      conv_lhs => rw [hdec y]
      exact hinv _ _ (QuotientAddGroup.eq.1 (QuotientAddGroup.out_eq' _)) _
    · by_contra hne
      obtain ⟨b, hb, hab⟩ := Set.mem_iUnion₂.1 (ht (hKs y hne))
      exact hT (Finset.mem_image.2 ⟨b, hb, QuotientAddGroup.eq.2 hab⟩)
  rw [key]
  refine Submodule.sum_mem _ fun q _ => ?_
  by_cases h0 : ∀ s, g q s = 0
  · have : GlobalTheory.WeilM.pureA F (g q) (ind q) = 0 := by
      funext y
      simp [GlobalTheory.WeilM.pureA, h0]
    rw [this]
    exact zero_mem _
  push_neg at h0
  obtain ⟨s0, hs0⟩ := h0
  refine Submodule.subset_span ⟨g q, ind q, ?_, rfl⟩
  let C : Set (Fin N → Af F) := {a | -q.out + a ∈ W}
  have hCcl : IsClosed C := hWcl.preimage (continuous_const.add continuous_id)
  have hCK : C ⊆ K := by
    intro a ha
    have h1 : Φ (ι a + embR s0) ≠ 0 := by
      rw [hinv _ _ ha, ← hg]
      exact hs0
    simpa [hfin] using hKs _ h1
  have hmk : IsLocallyConstant (fun a : Fin N → Af F => (a : (Fin N → Af F) ⧸ W)) :=
    (IsLocallyConstant.iff_exists_open _).2 fun x => ⟨{b | -b + x ∈ W},
      hWo.preimage (continuous_neg.add continuous_const), by simp, fun b hb => QuotientAddGroup.eq.2 hb⟩
  refine ⟨hmk.comp fun q' => if q' = q then (1 : ℂ) else 0, ?_⟩
  refine HasCompactSupport.intro' (hK.of_isClosed_subset hCcl hCK) hCcl fun x hx => ?_
  show (if (QuotientAddGroup.mk x : (Fin N → Af F) ⧸ W) = q then (1 : ℂ) else 0) = 0
  rw [if_neg]
  intro hq
  apply hx
  show -q.out + x ∈ W
  exact QuotientAddGroup.eq.1 (by rw [hq, QuotientAddGroup.out_eq'])

end GlobalTheory.LevelSchwartz

end
