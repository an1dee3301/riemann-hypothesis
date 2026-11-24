module

public import Mathlib
public import Init.Classical
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.PropLemmas
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Quotient
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Algebra.Star.Subalgebra
public import Mathlib.Analysis.CStarAlgebra.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.CStarAlgebra.ContinuousMap
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Quot
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.GroupTheory.Coset.Defs
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.Order.Basic
public import Mathlib.Order.BoundedOrder.Basic
public import Mathlib.Order.CompleteLattice.Defs
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Notation
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.LinearCombination.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.StarSubalgebra
public import Mathlib.Topology.Bases
public import Mathlib.Topology.CompactOpen
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.ContinuousMap.Algebra
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.ContinuousMap.Defs
public import Mathlib.Topology.ContinuousMap.Star
public import Mathlib.Topology.ContinuousMap.StoneWeierstrass
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Order
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

namespace GlobalTheory.QuotientDescentTwistedOperators

open Topology

noncomputable def desc {G : Type} [AddCommGroup G] [TopologicalSpace G] (Γ : AddSubgroup G)
    (f : G → ℂ) (hf : Continuous f) (hΓ : ∀ γ ∈ Γ, ∀ x, f (γ + x) = f x) : C(G ⧸ Γ, ℂ) where
  toFun := fun q => Quotient.liftOn' q f (by
    intro a b hab
    rw [QuotientAddGroup.leftRel_apply] at hab
    have := hΓ _ hab a
    rw [← this]
    congr 1
    abel)
  continuous_toFun := hf.quotient_liftOn' _

theorem desc_mk {G : Type} [AddCommGroup G] [TopologicalSpace G] (Γ : AddSubgroup G)
    (f : G → ℂ) (hf : Continuous f) (hΓ : ∀ γ ∈ Γ, ∀ x, f (γ + x) = f x) (x : G) :
    desc Γ f hf hΓ (QuotientAddGroup.mk x) = f x := rfl

theorem approx : ∀ (G : Type) [inst : AddCommGroup G] [inst_1 : TopologicalSpace G] [IsTopologicalAddGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [inst_6 : MeasurableSpace G] [BorelSpace G] (Γ : AddSubgroup G) [DiscreteTopology ↥Γ] (K : Set G), IsCompact K → (∀ (x : G), ∃ γ ∈ Γ, γ + x ∈ K) → ∀ (A : Type) [inst_9 : AddCommGroup A] (χ : A → G → ℂ), (∀ (a : A), Continuous (χ a)) → (∀ (a : A) (x y : G), χ a (x + y) = χ a x * χ a y) → (∀ (a b : A) (x : G), χ (a + b) x = χ a x * χ b x) → (∀ (x : G), χ (0 : A) x = (1 : ℂ)) → (∀ (a : A) (x : G), ‖χ a x‖ = (1 : ℝ)) → (∀ (x : G), (∀ (a : A), χ a x = (1 : ℂ)) ↔ x ∈ Γ) → ∀ (Φ : G → ℂ), Continuous Φ → (∀ γ ∈ Γ, ∀ (x : G), Φ (γ + x) = Φ x) → ∀ (ε : ℝ), (0 : ℝ) < ε → ∃ (s : Finset A) (c : A → ℂ), ∀ (x : G), ‖Φ x - ∑ a ∈ s, c a * χ a x‖ ≤ ε := by
  intro G _ _ _ _ _ _ _ _ Γ _ K hK hcov A _ χ hc hmulx hadd hzero hnorm hker Φ hΦ hΦinv ε hε

  have : CompactSpace (G ⧸ Γ) := by
    refine ⟨?_⟩
    have hU : (Set.univ : Set (G ⧸ Γ)) = QuotientAddGroup.mk '' K := by
      ext q
      refine QuotientAddGroup.induction_on q fun x => ?_
      obtain ⟨γ, hγ, hk⟩ := hcov x
      refine ⟨fun _ => ⟨γ + x, hk, ?_⟩, fun _ => Set.mem_univ _⟩
      rw [QuotientAddGroup.eq]
      have : -(γ + x) + x = -γ := by abel
      rw [this]
      exact Γ.neg_mem hγ
    rw [hU]
    exact hK.image continuous_quot_mk
  have hχ0 : ∀ a, χ a 0 = 1 := fun a => (hker 0).2 Γ.zero_mem a
  have hinv : ∀ a, ∀ γ ∈ Γ, ∀ x, χ a (γ + x) = χ a x := by
    intro a γ hγ x
    rw [hmulx, (hker γ).2 hγ a, one_mul]

  let e : A → C(G ⧸ Γ, ℂ) := fun a => desc Γ (χ a) (hc a) (hinv a)
  have he_apply : ∀ a x, e a (QuotientAddGroup.mk x) = χ a x := fun a x =>
    desc_mk Γ (χ a) (hc a) (hinv a) x
  have he_add : ∀ a b, e (a + b) = e a * e b := by
    intro a b
    ext q
    refine QuotientAddGroup.induction_on q fun x => ?_
    rw [ContinuousMap.mul_apply, he_apply, he_apply, he_apply, hadd]
  have he_zero : e 0 = 1 := by
    ext q
    refine QuotientAddGroup.induction_on q fun x => ?_
    rw [ContinuousMap.one_apply, he_apply, hzero]
  have he_star : ∀ a, star (e a) = e (-a) := by
    intro a
    ext q
    refine QuotientAddGroup.induction_on q fun x => ?_
    rw [ContinuousMap.star_apply, he_apply, he_apply]
    have h1 : χ (-a) x * χ a x = 1 := by rw [← hadd, neg_add_cancel, hzero]
    have h2 : χ a x * star (χ a x) = 1 := by
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hnorm]
      norm_num
    linear_combination (-(star (χ a x))) * h1 + χ (-a) x * h2

  let S : Submodule ℂ C(G ⧸ Γ, ℂ) := Submodule.span ℂ (Set.range e)
  have hone : (1 : C(G ⧸ Γ, ℂ)) ∈ S := he_zero ▸ Submodule.subset_span ⟨0, rfl⟩
  have hmul : ∀ f g, f ∈ S → g ∈ S → f * g ∈ S := by
    intro f g hf hg
    have h := Submodule.mul_mem_mul hf hg
    rw [Submodule.span_mul_span] at h
    refine (Submodule.span_le.mpr ?_) h
    rintro _ ⟨_, ⟨a, rfl⟩, _, ⟨b, rfl⟩, rfl⟩
    exact Submodule.subset_span ⟨a + b, he_add a b⟩
  have hstar : ∀ f ∈ S, star f ∈ S := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      exact Submodule.subset_span ⟨-a, (he_star a).symm⟩
    | zero => rw [star_zero]; exact S.zero_mem
    | add x y _ _ hx hy => rw [star_add]; exact S.add_mem hx hy
    | smul c x _ hx => rw [star_smul]; exact S.smul_mem _ hx
  let B : StarSubalgebra ℂ C(G ⧸ Γ, ℂ) :=
    { carrier := S
      mul_mem' := fun {f g} hf hg => hmul f g hf hg
      one_mem' := hone
      add_mem' := fun hf hg => S.add_mem hf hg
      zero_mem' := S.zero_mem
      algebraMap_mem' := fun c => by
        rw [Algebra.algebraMap_eq_smul_one]
        exact S.smul_mem c hone
      star_mem' := fun {f} hf => hstar f hf }

  have hsep : B.SeparatesPoints := by
    intro q₁ q₂
    refine QuotientAddGroup.induction_on q₁ fun x => QuotientAddGroup.induction_on q₂ fun y => ?_
    intro hne
    have hex : ∃ a, χ a x ≠ χ a y := by
      by_contra hall
      simp only [not_exists, ne_eq, not_not] at hall
      apply hne
      rw [QuotientAddGroup.eq]
      refine (hker _).1 fun a => ?_
      rw [hmulx, ← hall a, ← hmulx, neg_add_cancel, hχ0 a]
    obtain ⟨a, ha⟩ := hex
    refine ⟨e a, ⟨e a, Submodule.subset_span ⟨a, rfl⟩, rfl⟩, ?_⟩
    rwa [he_apply, he_apply]

  have hB := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints B hsep
  let Φq : C(G ⧸ Γ, ℂ) := desc Γ Φ hΦ hΦinv
  have hmem : Φq ∈ closure (B : Set C(G ⧸ Γ, ℂ)) := by
    rw [← StarSubalgebra.topologicalClosure_coe, hB]
    trivial
  obtain ⟨g, hg, hdist⟩ := Metric.mem_closure_iff.mp hmem ε hε
  obtain ⟨c, hcg⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp (show g ∈ S from hg)
  refine ⟨c.support, c, fun x => ?_⟩
  have hval : ∑ a ∈ c.support, c a * χ a x = g (QuotientAddGroup.mk x) := by
    rw [← hcg, Finsupp.sum, ContinuousMap.coe_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [ContinuousMap.smul_apply, he_apply, smul_eq_mul]
  rw [hval, ← desc_mk Γ Φ hΦ hΦinv x]
  calc ‖Φq (QuotientAddGroup.mk x) - g (QuotientAddGroup.mk x)‖
      = ‖(Φq - g) (QuotientAddGroup.mk x)‖ := rfl
    _ ≤ ‖Φq - g‖ := ContinuousMap.norm_coe_le_norm _ _
    _ = dist Φq g := (dist_eq_norm _ _).symm
    _ ≤ ε := hdist.le

end GlobalTheory.QuotientDescentTwistedOperators
