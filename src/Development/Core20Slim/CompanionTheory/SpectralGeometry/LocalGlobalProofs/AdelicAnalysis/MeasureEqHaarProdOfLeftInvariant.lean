module

public import Mathlib
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Order.IsBotOne
public import Mathlib.Algebra.Order.Monoid.Canonical.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Basic.Countable.Defs
public import Mathlib.Basic.ENNReal.Action
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.ENNReal.Inv
public import Mathlib.Basic.ENNReal.Operations
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.SProd
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Set.BooleanAlgebra
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Lattice.Indexed
public import Mathlib.Data.Set.Operations
public import Mathlib.Data.Set.Prod
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Group.Arithmetic
public import Mathlib.MeasureTheory.Group.Defs
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Module
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.Regular
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.MeasureTheory.OuterMeasure.Basic
public import Mathlib.MeasureTheory.PiSystem
public import Mathlib.Order.Basic
public import Mathlib.Order.CompleteBooleanAlgebra
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Notation
public import Mathlib.Order.RelClasses
public import Mathlib.Order.SetNotation
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Closure
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.Compactness.Paracompact
public import Mathlib.Topology.Compactness.SigmaCompact
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Metrizable.Basic
public import Mathlib.Topology.Metrizable.Urysohn
public import Mathlib.Topology.Neighborhoods
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.Separation.Regular

@[expose] public section

open MeasureTheory Topology Matrix
open scoped ENNReal NNReal

namespace GlobalTheory.CompanionTheory.SW.InvariantProduct

theorem exists_const_rect {Q Z : Type} [Group Q] [TopologicalSpace Q] [LocallyCompactSpace Q]
    [SecondCountableTopology Q] [T2Space Q] [MeasurableSpace Q] [BorelSpace Q]
    [IsTopologicalGroup Q] [TopologicalSpace Z] [T2Space Z]
    [MeasurableSpace Z] [BorelSpace Z] (η : Measure Q) [η.IsHaarMeasure]
    (ρ : Measure (Q × Z)) [IsLocallyFiniteMeasure ρ]
    (hinv : ∀ q : Q, ρ.map (fun p => (q * p.1, p.2)) = ρ)
    {A C : Set Z} (hA : MeasurableSet A) (hC : IsCompact C) (hAC : A ⊆ C) :
    ∃ c : ℝ≥0, ∀ U : Set Q, MeasurableSet U → ρ (U ×ˢ A) = c * η U := by
  let μ : Measure Q := (ρ.restrict (Set.univ ×ˢ A)).map Prod.fst
  have hμ : ∀ U : Set Q, MeasurableSet U → μ U = ρ (U ×ˢ A) := by
    intro U hU
    rw [Measure.map_apply measurable_fst hU, Measure.restrict_apply (measurable_fst hU)]
    congr 1
    ext ⟨x, z⟩
    simp
  haveI : μ.IsMulLeftInvariant := ⟨fun q => by
    ext U hU
    have hT : Measurable (fun p : Q × Z => (q * p.1, p.2)) :=
      (measurable_fst.const_mul q).prodMk measurable_snd
    rw [Measure.map_apply (measurable_const_mul q) hU, hμ _ (measurable_const_mul q hU), hμ U hU]
    conv_rhs => rw [← hinv q]
    rw [Measure.map_apply hT (hU.prod hA)]
    rfl⟩
  haveI : IsFiniteMeasureOnCompacts μ := ⟨fun L hL => by
    rw [hμ L hL.isClosed.measurableSet]
    exact (measure_mono (Set.prod_mono subset_rfl hAC)).trans_lt (hL.prod hC).measure_lt_top⟩
  refine ⟨Measure.haarScalarFactor μ η, fun U hU => ?_⟩
  have h := congrArg (fun ν : Measure Q => ν U) (Measure.isMulLeftInvariant_eq_smul μ η)
  simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h
  rw [← hμ U hU]
  exact h

end GlobalTheory.CompanionTheory.SW.InvariantProduct

namespace GlobalTheory.CompanionTheory.SW

theorem measure_eq_haar_prod_of_left_invariant :
    ∀ (Q Z : Type) [Group Q] [TopologicalSpace Q] [LocallyCompactSpace Q]
      [SecondCountableTopology Q] [T2Space Q] [MeasurableSpace Q] [BorelSpace Q]
      [IsTopologicalGroup Q] [TopologicalSpace Z] [LocallyCompactSpace Z]
      [SecondCountableTopology Z] [T2Space Z] [MeasurableSpace Z] [BorelSpace Z]
      (η : Measure Q) [η.IsHaarMeasure] (ρ : Measure (Q × Z)) [IsLocallyFiniteMeasure ρ],
      (∀ q : Q, ρ.map (fun p => (q * p.1, p.2)) = ρ) →
        ∃ m : Measure Z, IsLocallyFiniteMeasure m ∧ ρ = η.prod m := by
  intro Q Z _ _ _ _ _ _ _ _ _ _ _ _ _ _ η _ ρ _ hinv
  obtain ⟨K, hKc, hK1⟩ := exists_compact_mem_nhds (1 : Q)
  have hKpos : η K ≠ 0 := (lt_of_lt_of_le (isOpen_interior.measure_pos η ⟨1, mem_interior_iff_mem_nhds.2 hK1⟩)
    (measure_mono interior_subset)).ne'
  have hKfin : η K ≠ ∞ := hKc.measure_lt_top.ne
  have hKm : MeasurableSet K := hKc.isClosed.measurableSet
  let m : Measure Z := (η K)⁻¹ • (ρ.restrict (K ×ˢ Set.univ)).map Prod.snd
  have hm : ∀ A : Set Z, MeasurableSet A → m A = (η K)⁻¹ * ρ (K ×ˢ A) := by
    intro A hA
    have hset : Prod.snd ⁻¹' A ∩ (K ×ˢ (Set.univ : Set Z)) = K ×ˢ A := by
      ext ⟨x, z⟩
      simp [and_comm]
    simp only [m, Measure.smul_apply, smul_eq_mul]
    rw [Measure.map_apply measurable_snd hA, Measure.restrict_apply (measurable_snd hA), hset]
  have hrect : ∀ (U : Set Q) (A C : Set Z), MeasurableSet U → MeasurableSet A → IsCompact C →
      A ⊆ C → ρ (U ×ˢ A) = η U * m A := by
    intro U A C hU hA hC hAC
    obtain ⟨c, hc⟩ := InvariantProduct.exists_const_rect η ρ hinv hA hC hAC
    rw [hc U hU, hm A hA, hc K hKm, ← mul_assoc (η K)⁻¹, mul_comm (η K)⁻¹,
      mul_assoc (c : ℝ≥0∞), ENNReal.inv_mul_cancel hKpos hKfin, mul_one, mul_comm]
  have hmC : ∀ C : Set Z, IsCompact C → m C < ∞ := by
    intro C hC
    rw [hm C hC.isClosed.measurableSet]
    exact ENNReal.mul_lt_top (ENNReal.inv_lt_top.2 (pos_iff_ne_zero.2 hKpos))
      (hKc.prod hC).measure_lt_top
  haveI hmfc : IsFiniteMeasureOnCompacts m := ⟨fun C hC => hmC C hC⟩
  refine ⟨m, inferInstance, ?_⟩
  symm
  let CQ : Set (Set Q) := {U | MeasurableSet U ∧ ∃ L, IsCompact L ∧ U ⊆ L}
  let CZ : Set (Set Z) := {A | MeasurableSet A ∧ ∃ L, IsCompact L ∧ A ⊆ L}
  have genAux : ∀ (X : Type) [TopologicalSpace X] [SigmaCompactSpace X] [T2Space X]
      [MeasurableSpace X] [BorelSpace X],
      MeasurableSpace.generateFrom {U : Set X | MeasurableSet U ∧ ∃ L, IsCompact L ∧ U ⊆ L} =
        ‹MeasurableSpace X› := by
    intro X _ _ _ M _
    apply le_antisymm
    · exact MeasurableSpace.generateFrom_le fun U hU => hU.1
    · intro B hB
      have : B = ⋃ n, B ∩ compactCovering X n := by
        rw [← Set.inter_iUnion, iUnion_compactCovering, Set.inter_univ]
      rw [this]
      exact MeasurableSet.iUnion fun n => MeasurableSpace.measurableSet_generateFrom
        ⟨hB.inter (isCompact_compactCovering X n).isClosed.measurableSet,
          _, isCompact_compactCovering X n, Set.inter_subset_right⟩
  have piAux : ∀ (X : Type) [TopologicalSpace X] [MeasurableSpace X],
      IsPiSystem {U : Set X | MeasurableSet U ∧ ∃ L, IsCompact L ∧ U ⊆ L} := by
    intro X _ _ U hU V hV _
    obtain ⟨hUm, L, hL, hUL⟩ := hU
    exact ⟨hUm.inter hV.1, L, hL, Set.inter_subset_left.trans hUL⟩
  have spanAux : ∀ (X : Type) [TopologicalSpace X] [SigmaCompactSpace X] [T2Space X]
      [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsFiniteMeasureOnCompacts μ],
      μ.FiniteSpanningSetsIn {U : Set X | MeasurableSet U ∧ ∃ L, IsCompact L ∧ U ⊆ L} := by
    intro X _ _ _ _ _ μ _
    exact ⟨compactCovering X,
      fun n => ⟨(isCompact_compactCovering X n).isClosed.measurableSet, _,
        isCompact_compactCovering X n, subset_rfl⟩,
      fun n => (isCompact_compactCovering X n).measure_lt_top,
      iUnion_compactCovering X⟩
  refine Measure.prod_eq_generateFrom (genAux Q) (genAux Z) (piAux Q) (piAux Z)
    (spanAux Q η) (spanAux Z m) ?_
  rintro U ⟨hU, -⟩ A ⟨hA, L, hL, hAL⟩
  exact (hrect U A L hU hA hL hAL)

end GlobalTheory.CompanionTheory.SW
