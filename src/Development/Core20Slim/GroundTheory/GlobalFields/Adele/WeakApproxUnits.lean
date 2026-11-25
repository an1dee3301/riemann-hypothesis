module

public import Mathlib
public import Development.Core20Slim.GroundTheory.GlobalFields.Adele.WeakApprox
public import Init.Classical
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Subtype.Basic
public import Init.Data.Zero
public import Init.Ext
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Algebra.Group.WithOne.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Field.WithAbs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.Normed.Ring.WithAbs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.IsEmpty.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Sets
public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Logic.Function.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.Order.SetNotation
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.GroupWithZero
public import Mathlib.Topology.Algebra.Valued.NormedValued
public import Mathlib.Topology.Algebra.Valued.ValuedField
public import Mathlib.Topology.Basic
public import Mathlib.Topology.Closure
public import Mathlib.Topology.Connected.Separation
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Maps.Basic
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
public import Mathlib.Topology.Metrizable.Basic
public import Mathlib.Topology.Metrizable.Uniformity
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.UniformSpace.Defs

set_option synthInstance.maxHeartbeats 400000

@[expose] public section

namespace GroundTheory.Global

open IsDedekindDomain NumberField Topology

variable {K : Type*} [Field K] [NumberField K]
  (S : Finset (HeightOneSpectrum (𝓞 K))) (T : Finset (InfinitePlace K))

theorem denseRange_units_prod_pi :
    DenseRange (fun a : Kˣ ↦
      ((fun v : S ↦ Units.map (algebraMap K (v.1.adicCompletion K)).toMonoidHom a),
        (fun w : T ↦ Units.map (algebraMap K w.1.Completion).toMonoidHom a))) := by
  classical
  set f := fun a : Kˣ ↦
      ((fun v : S ↦ Units.map (algebraMap K (v.1.adicCompletion K)).toMonoidHom a),
        (fun w : T ↦ Units.map (algebraMap K w.1.Completion).toMonoidHom a)) with hf
  set E : ((v : S) → (v.1.adicCompletion K)ˣ) × ((w : T) → (w.1.Completion)ˣ) →
      ((v : S) → v.1.adicCompletion K) × ((w : T) → w.1.Completion) :=
    Prod.map (Pi.map fun _ ↦ Units.val) (Pi.map fun _ ↦ Units.val) with hE
  have hEi : IsInducing E :=
    (IsInducing.piMap fun _ ↦ Units.isEmbedding_val₀.isInducing).prodMap
      (IsInducing.piMap fun _ ↦ Units.isEmbedding_val₀.isInducing)
  let W : Set (((v : S) → v.1.adicCompletion K) × ((w : T) → w.1.Completion)) :=
    {z | (∀ v, z.1 v ≠ 0) ∧ ∀ w, z.2 w ≠ 0}
  have hW : IsOpen W := by
    have : W = (⋂ v, {z | z.1 v ≠ 0}) ∩ ⋂ w, {z | z.2 w ≠ 0} := by
      ext z; simp [W]
    rw [this]
    exact (isOpen_iInter_of_finite fun v ↦
      isOpen_ne_fun ((continuous_apply v).comp continuous_fst) continuous_const).inter
      (isOpen_iInter_of_finite fun w ↦
        isOpen_ne_fun ((continuous_apply w).comp continuous_snd) continuous_const)
  refine dense_iff_inter_open.2 fun U hU ⟨u, hu⟩ ↦ ?_
  obtain ⟨V, hV, rfl⟩ := hEi.isOpen_iff.1 hU
  have hEu : E u ∈ W := ⟨fun v ↦ (u.1 v).ne_zero, fun w ↦ (u.2 w).ne_zero⟩
  obtain ⟨x, hxV, hxW⟩ := (denseRange_algebraMap_prod_pi S T).exists_mem_open (hV.inter hW)
    ⟨E u, hu, hEu⟩
  by_cases hx : x = 0
  · have hS : IsEmpty S := ⟨fun v ↦ hxW.1 v (by rw [hx]; exact map_zero _)⟩
    have hT : IsEmpty T := ⟨fun w ↦ hxW.2 w (by rw [hx]; exact map_zero _)⟩
    refine ⟨f 1, ?_, 1, rfl⟩
    show E (f 1) ∈ V
    convert hxV using 1
    exact Prod.ext (funext fun v ↦ isEmptyElim v) (funext fun w ↦ isEmptyElim w)
  · refine ⟨f (Units.mk0 x hx), ?_, _, rfl⟩
    exact hxV

end GroundTheory.Global
