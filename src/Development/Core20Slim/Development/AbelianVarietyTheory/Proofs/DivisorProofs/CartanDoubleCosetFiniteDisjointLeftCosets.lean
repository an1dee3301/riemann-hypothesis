module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
public import Development.Core20Slim.Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ScaledIntegerPeriodic
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EventuallyDeepSubset
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Init.Classical
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Basic.SProd
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Finset.Sigma
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Set.BooleanAlgebra
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Disjoint
public import Mathlib.Data.Set.Function
public import Mathlib.Data.Set.Lattice.Indexed
public import Mathlib.Data.Set.Operations
public import Mathlib.Data.Set.Pairwise.Basic
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Logic.Function.Defs
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.Order.BoundedOrder.Basic
public import Mathlib.Order.CompleteBooleanAlgebra
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Disjoint
public import Mathlib.Order.SetNotation
public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
public import Mathlib.Tactic.Group
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Instances.Matrix

@[expose] public section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.KSplit
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instMeasMat
open GlobalTheory.IndefiniteRowSideFullHecke.ScaledIntegerPeriodic

namespace GlobalTheory.ShellCosets

theorem piece_eq_of_mem {G : Type*} [Group G] (K : Subgroup G) {c c' g : G}
    (h1 : c⁻¹ * g ∈ K) (h2 : c'⁻¹ * g ∈ K) :
    {h : G | c⁻¹ * h ∈ K} = {h : G | c'⁻¹ * h ∈ K} := by
  ext h
  simp only [Set.mem_setOf_eq]
  constructor
  · intro hh
    have := K.mul_mem (K.mul_mem h2 (K.inv_mem h1)) hh
    simpa [mul_assoc] using this
  · intro hh
    have := K.mul_mem (K.mul_mem h1 (K.inv_mem h2)) hh
    simpa [mul_assoc] using this

theorem shell_cosets : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ϖ : kˣ) (a : ℕ) (n : Fin a → ℤ), ∃ t : Finset (GL (Fin a) k), (∀ x ∈ t, x ∈ KO k (Fin a)) ∧
      shellSet ϖ n = ⋃ x ∈ t, {g : GL (Fin a) k | (x * diagGL (fun i => ϖ ^ n i))⁻¹ * g ∈ KO k (Fin a)} ∧
      (t : Set (GL (Fin a) k)).PairwiseDisjoint
        (fun x => {g : GL (Fin a) k | (x * diagGL (fun i => ϖ ^ n i))⁻¹ * g ∈ KO k (Fin a)}) := by
  intro k _ _ _ _ ϖ a n
  classical
  set d : GL (Fin a) k := diagGL (fun i => ϖ ^ n i) with hd
  set K := KO k (Fin a) with hK
  set P : GL (Fin a) k → Set (GL (Fin a) k) := fun x => {g | (x * d)⁻¹ * g ∈ K} with hP
  have hPo : ∀ x, IsOpen (P x) := fun x =>
    (GlobalTheory.SplitFlip.isOpen_KO (k := k) (n := Fin a)).preimage (continuous_const_mul _)
  have hsub : ∀ x ∈ K, P x ⊆ shellSet ϖ n := by
    intro x hx g hg
    rw [mem_shellSet]
    exact ⟨x, hx, _, hg, by rw [← hd]; group⟩
  have himg : shellSet ϖ n = (fun p : GL (Fin a) k × GL (Fin a) k => p.1 * d * p.2) '' ((K : Set _) ×ˢ (K : Set _)) := by
    ext g
    rw [mem_shellSet]
    constructor
    · rintro ⟨x, hx, y, hy, rfl⟩; exact ⟨(x, y), ⟨hx, hy⟩, rfl⟩
    · rintro ⟨⟨x, y⟩, ⟨hx, hy⟩, rfl⟩; exact ⟨x, hx, y, hy, rfl⟩
  have hcomp : IsCompact (shellSet ϖ n) := by
    rw [himg]
    exact (GlobalTheory.SplitFlip.isCompact_KO.prod GlobalTheory.SplitFlip.isCompact_KO).image (by fun_prop)
  have hcov : shellSet ϖ n ⊆ ⋃ x : K, P x := by
    intro g hg
    obtain ⟨x, hx, y, hy, rfl⟩ := mem_shellSet.mp hg
    refine Set.mem_iUnion.mpr ⟨⟨x, hx⟩, ?_⟩
    show (x * d)⁻¹ * (x * (diagGL fun i => ϖ ^ n i) * y) ∈ K
    rw [← hd]
    convert hy using 1
    group
  obtain ⟨s, hs⟩ := hcomp.elim_finite_subcover (fun x : K => P x) (fun x => hPo x) hcov
  let s' : Finset (GL (Fin a) k) := s.image Subtype.val
  have hs'K : ∀ x ∈ s', x ∈ K := by
    intro x hx; obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hx; exact y.2
  let r : Set (GL (Fin a) k) → GL (Fin a) k := Function.invFunOn P (s' : Set _)
  let t : Finset (GL (Fin a) k) := (s'.image P).image r
  have hr : ∀ x ∈ s', r (P x) ∈ s' ∧ P (r (P x)) = P x := fun x hx =>
    ⟨Function.invFunOn_mem ⟨x, hx, rfl⟩, Function.invFunOn_eq ⟨x, hx, rfl⟩⟩
  have ht : ∀ y ∈ t, ∃ x ∈ s', y = r (P x) := by
    intro y hy
    obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hQ
    exact ⟨x, hx, rfl⟩
  refine ⟨t, ?_, ?_, ?_⟩
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := ht y hy
    exact hs'K _ (hr x hx).1
  · apply Set.Subset.antisymm
    · intro g hg
      obtain ⟨x, hxs, hgx⟩ := Set.mem_iUnion₂.mp (hs hg)
      have hx' : (x : GL (Fin a) k) ∈ s' := Finset.mem_image_of_mem _ hxs
      refine Set.mem_iUnion₂.mpr ⟨r (P x), Finset.mem_image_of_mem _ (Finset.mem_image_of_mem _ hx'), ?_⟩
      show g ∈ P (r (P x))
      rw [(hr _ hx').2]; exact hgx
    · intro g hg
      obtain ⟨y, hy, hgy⟩ := Set.mem_iUnion₂.mp hg
      obtain ⟨x, hx, rfl⟩ := ht y hy
      exact hsub _ (hs'K _ (hr x hx).1) hgy
  · intro y hy y' hy' hne
    obtain ⟨x, hx, rfl⟩ := ht y hy
    obtain ⟨x', hx', rfl⟩ := ht y' hy'
    rw [Function.onFun, Set.disjoint_left]
    intro g hg hg'
    apply hne
    have := piece_eq_of_mem K hg hg'
    change P (r (P x)) = P (r (P x')) at this
    rw [(hr x hx).2, (hr x' hx').2] at this
    rw [this]

end GlobalTheory.ShellCosets
