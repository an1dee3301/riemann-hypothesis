module

public import Mathlib
public import Init.BinderNameHint
public import Init.Classical
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Basic.Countable.Defs
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SProd
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Set.BooleanAlgebra
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Disjoint
public import Mathlib.Data.Set.Lattice.Indexed
public import Mathlib.Data.Set.Operations
public import Mathlib.Logic.Function.Defs
public import Mathlib.Logic.Pairwise
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Group.Arithmetic
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.MeasurableSpace.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.NullMeasurable
public import Mathlib.MeasureTheory.Measure.Regular
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.MeasureTheory.OuterMeasure.Basic
public import Mathlib.Order.BoundedOrder.Basic
public import Mathlib.Order.CompleteBooleanAlgebra
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Disjoint
public import Mathlib.Order.Notation
public import Mathlib.Order.SetNotation
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Push
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.SummationFilter
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.Compactness.Paracompact
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Metrizable.Basic
public import Mathlib.Topology.Metrizable.Urysohn
public import Mathlib.Topology.Order.Real
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.Separation.Regular

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.Adelic

theorem lattice_pigeonhole_measure_preserving :
    ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [T2Space V]
      [LocallyCompactSpace V] [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V]
      (μ : Measure V) [μ.IsAddHaarMeasure], μ Set.univ = ⊤ →
      ∀ (Λ : Type) [AddCommGroup Λ] [Countable Λ] (j : Λ →+ V) (C : Set V), IsCompact C →
        (∀ y, ∃ l, y - j l ∈ C) →
        ∃ Ω : Set V, IsCompact Ω ∧ ∀ e : V →+ V, Continuous e → μ.map e = μ →
          ∃ l, l ≠ 0 ∧ e (j l) ∈ Ω := by
  intro V _ _ _ _ _ _ _ _ μ _ htop Λ _ _ j C hC hcov
  have hCfin : μ C < ⊤ := hC.measure_lt_top
  obtain ⟨K, -, hKc, hK⟩ :=
    isOpen_univ.exists_lt_isCompact (μ := μ) (r := μ C) (by rw [htop]; exact hCfin)
  refine ⟨(fun p : V × V => p.1 - p.2) '' (K ×ˢ K),
    (hKc.prod hKc).image (continuous_fst.sub continuous_snd), fun e he hμ => ?_⟩
  by_contra hno
  push_neg at hno
  have hKm : MeasurableSet K := hKc.isClosed.measurableSet
  have hem : Measurable e := he.measurable
  have hAm : MeasurableSet (e ⁻¹' K) := hem hKm
  have hμA : μ (e ⁻¹' K) = μ K := by
    have h := Measure.map_apply (μ := μ) hem hKm
    rw [hμ] at h
    exact h.symm

  let S : Λ → Set V := fun l => ((fun x => x + j l) ⁻¹' (e ⁻¹' K)) ∩ C
  have hCm : MeasurableSet C := hC.isClosed.measurableSet
  have hSm : ∀ l, MeasurableSet (S l) := fun l =>
    (hAm.preimage (measurable_add_const (j l))).inter hCm
  have hdisj : Pairwise (Function.onFun Disjoint S) := by
    intro l l' hll
    refine Set.disjoint_left.2 ?_
    rintro x ⟨hx, -⟩ ⟨hx', -⟩
    have hne : l - l' ≠ 0 := sub_ne_zero.2 hll
    refine hno _ hne ?_
    have hx1 : e (x + j l) ∈ K := hx
    have hx2 : e (x + j l') ∈ K := hx'
    have : e (j (l - l')) = e (x + j l) - e (x + j l') := by
      rw [← map_sub, map_sub j]
      congr 1
      abel
    rw [this]
    exact ⟨(e (x + j l), e (x + j l')), ⟨hx1, hx2⟩, rfl⟩
  have hcover : e ⁻¹' K ⊆ ⋃ l, (e ⁻¹' K) ∩ ((fun x => x - j l) ⁻¹' C) := by
    intro y hy
    obtain ⟨l, hl⟩ := hcov y
    exact Set.mem_iUnion.2 ⟨l, hy, hl⟩
  have hpiece : ∀ l, μ ((e ⁻¹' K) ∩ ((fun x => x - j l) ⁻¹' C)) = μ (S l) := by
    intro l
    have hS : S l = (fun x => x + j l) ⁻¹' ((e ⁻¹' K) ∩ ((fun x => x - j l) ⁻¹' C)) := by
      ext x
      simp [S]
    rw [hS, measure_preimage_add_right]
  have hle : μ K ≤ μ C := by
    calc μ K = μ (e ⁻¹' K) := hμA.symm
      _ ≤ μ (⋃ l, (e ⁻¹' K) ∩ ((fun x => x - j l) ⁻¹' C)) := measure_mono hcover
      _ ≤ ∑' l, μ ((e ⁻¹' K) ∩ ((fun x => x - j l) ⁻¹' C)) := measure_iUnion_le _
      _ = ∑' l, μ (S l) := by simp_rw [hpiece]
      _ = μ (⋃ l, S l) := (measure_iUnion hdisj hSm).symm
      _ ≤ μ C := measure_mono (Set.iUnion_subset fun l => Set.inter_subset_right)
  exact absurd hK (not_lt.2 hle)

end GlobalTheory.CompanionTheory.Adelic
