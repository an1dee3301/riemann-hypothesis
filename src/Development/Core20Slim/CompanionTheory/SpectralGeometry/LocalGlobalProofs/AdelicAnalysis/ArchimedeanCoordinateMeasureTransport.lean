module

public import Mathlib
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GaussQ
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHomeomorphRankOneTuplesStatement
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteAdelesLocalRingTotallyRealStatement
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import Init.Core
public import Init.Data.Fin.Basic
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.PropLemmas
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Order.Lattice
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.RCLike.Lemmas
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Countable.Defs
public import Mathlib.Basic.ENNReal.Action
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.ENNReal.Real
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Group.Arithmetic
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.MeasurableSpace.Embedding
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Module
public import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.RingTheory.Artinian.Defs
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.BB.InfPush

theorem map_swap_volume (ι κ : Type) [Fintype ι] [Fintype κ] :
    (volume : Measure (ι → κ → ℝ)).map (fun f k i => f i k) = (volume : Measure (κ → ι → ℝ)) := by
  let s : (ι → κ → ℝ) ≃+ (κ → ι → ℝ) :=
    { toFun := fun f k i => f i k
      invFun := fun g i k => g k i
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl }
  have hs : Continuous s := continuous_pi fun k => continuous_pi fun i =>
    (continuous_apply k).comp (continuous_apply i)
  have hs' : Continuous s.symm := continuous_pi fun i => continuous_pi fun k =>
    (continuous_apply i).comp (continuous_apply k)
  have h0 : (volume : Measure (κ → ℝ)).IsAddHaarMeasure := by
    rw [volume_pi]; exact Measure.pi.isAddHaarMeasure _
  have h0' : (volume : Measure (ι → ℝ)).IsAddHaarMeasure := by
    rw [volume_pi]; exact Measure.pi.isAddHaarMeasure _
  have hV : (volume : Measure (ι → κ → ℝ)).IsAddHaarMeasure := by
    rw [volume_pi]; exact Measure.pi.isAddHaarMeasure _
  have hV' : (volume : Measure (κ → ι → ℝ)).IsAddHaarMeasure := by
    rw [volume_pi]; exact Measure.pi.isAddHaarMeasure _
  have hH : ((volume : Measure (ι → κ → ℝ)).map s).IsAddHaarMeasure :=
    s.isAddHaarMeasure_map _ hs hs'
  have hc := Measure.isAddLeftInvariant_eq_smul ((volume : Measure (ι → κ → ℝ)).map s)
    (volume : Measure (κ → ι → ℝ))
  set c := Measure.addHaarScalarFactor ((volume : Measure (ι → κ → ℝ)).map s)
    (volume : Measure (κ → ι → ℝ)) with hcdef
  let B : Set (κ → ι → ℝ) := Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Set.Icc 0 1
  let B' : Set (ι → κ → ℝ) := Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Set.Icc 0 1
  have hB : MeasurableSet B := MeasurableSet.univ_pi fun _ => MeasurableSet.univ_pi fun _ =>
    measurableSet_Icc
  have hpre : s ⁻¹' B = B' := by
    ext f
    simp only [B, B', Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies]
    exact forall_comm
  have vB : (volume : Measure (κ → ι → ℝ)) B = 1 := by
    simp only [B]
    rw [volume_pi_pi]
    refine Finset.prod_eq_one fun _ _ => ?_
    rw [volume_pi_pi]
    refine Finset.prod_eq_one fun _ _ => ?_
    simp
  have vB' : (volume : Measure (ι → κ → ℝ)) B' = 1 := by
    simp only [B']
    rw [volume_pi_pi]
    refine Finset.prod_eq_one fun _ _ => ?_
    rw [volume_pi_pi]
    refine Finset.prod_eq_one fun _ _ => ?_
    simp
  have h1 : ((volume : Measure (ι → κ → ℝ)).map s) B = 1 := by
    rw [Measure.map_apply hs.measurable hB, hpre, vB']
  have hc1 : c = 1 := by
    rw [hc] at h1
    simp only [Measure.smul_apply, vB] at h1
    simpa using h1
  rw [hc1, one_smul] at hc
  exact hc

theorem pi_smul_const {ι α : Type} [Fintype ι] [MeasurableSpace α] (ν : Measure α) [SigmaFinite ν]
    (c : ℝ≥0) :
    Measure.pi (fun _ : ι => (c : ℝ≥0∞) • ν) =
      ((c : ℝ≥0∞) ^ Fintype.card ι) • Measure.pi fun _ : ι => ν := by
  have : SigmaFinite ((c : ℝ≥0∞) • ν) := by
    rw [← ENNReal.smul_def]; infer_instance
  refine Measure.pi_eq fun s hs => ?_
  simp only [Measure.smul_apply, Measure.pi_pi, smul_eq_mul, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ]

theorem map_coord_pi {ι κ A : Type} [Fintype ι] [Fintype κ] [MeasurableSpace A]
    (lam : Measure A) [SigmaFinite lam] (e : A → κ → ℝ) (he : Measurable e) (c : ℝ≥0)
    (hlam : lam.map e = (c : ℝ≥0∞) • (volume : Measure (κ → ℝ))) :
    (Measure.pi fun _ : ι => lam).map (fun y w p => e (y p) w) =
      ((c : ℝ≥0∞) ^ Fintype.card ι) • (volume : Measure (κ → ι → ℝ)) := by
  have hsf : SigmaFinite (lam.map e) := by
    rw [hlam, ← ENNReal.smul_def]; infer_instance
  have h1 : (Measure.pi fun _ : ι => lam).map (fun y p => e (y p)) =
      Measure.pi fun _ : ι => lam.map e :=
    Measure.pi_map_pi (fun _ => he.aemeasurable)
  have hsw : Measurable (fun (f : ι → κ → ℝ) (w : κ) (p : ι) => f p w) :=
    measurable_pi_iff.2 fun w => measurable_pi_iff.2 fun p =>
      (measurable_pi_apply w).comp (measurable_pi_apply p)
  have hc : Measurable (fun (y : ι → A) (p : ι) => e (y p)) :=
    measurable_pi_iff.2 fun p => he.comp (measurable_pi_apply p)
  have h2 : (fun (y : ι → A) (w : κ) (p : ι) => e (y p) w) =
      (fun (f : ι → κ → ℝ) (w : κ) (p : ι) => f p w) ∘ (fun (y : ι → A) (p : ι) => e (y p)) := rfl
  rw [h2, ← Measure.map_map hsw hc, h1, hlam, pi_smul_const,
    Measure.map_smul _ hsw.aemeasurable, ← volume_pi, map_swap_volume]

end GlobalTheory.CompanionTheory.SW.BB.InfPush


open GlobalTheory.CompanionTheory.SW.BB.InfPush in
theorem GlobalTheory.CompanionTheory.SW.BB.infPush : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M d : ℕ) (b : Module.Basis (Fin d) F E) (e : Ainf F ≃+* (InfinitePlace F → ℝ)), IsHomeomorph e → ∀ (laminf : Measure (Ainf F)), laminf.IsAddHaarMeasure → laminf.map e = ENNReal.ofReal (Real.sqrt |(discr F : ℝ)|)⁻¹ • (volume : Measure (InfinitePlace F → ℝ)) → (coordW (Ainf F) b laminf 1 M).map (fun X w => xw e b X w) = ENNReal.ofReal ((Real.sqrt |(discr F : ℝ)|)⁻¹ ^ (M * d)) • (volume : Measure (InfinitePlace F → Fin M × Fin d → ℝ)) := by
  intro F E _ _ _ _ _ σ hσ M d b e he laminf hH hmap
  have hloc := GlobalTheory.T.infinite_adeles_local_ring_totally_real F hσ.1
  obtain ⟨h1, h2, h3, h4, -⟩ := hloc
  haveI := h1
  haveI := h2
  haveI := h3
  haveI := h4
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  obtain ⟨-, hemb, hcoord⟩ := GlobalTheory.T.coordinate_homeomorph_rank_one_tuples F E σ hσ (Ainf F) d b laminf hH M
  have hem : Measurable (fun x : Ainf F => (e x : InfinitePlace F → ℝ)) := he.continuous.measurable
  have hΦ : Measurable (fun (y : Fin M × Fin d → Ainf F) (w : InfinitePlace F) (p : Fin M × Fin d) => e (y p) w) :=
    measurable_pi_iff.2 fun w => measurable_pi_iff.2 fun p =>
      (measurable_pi_apply w).comp (hem.comp (measurable_pi_apply p))
  have hcomp : (fun (X : Fin 1 → Fin M → Ainf F ⊗[F] E) (w : InfinitePlace F) => xw e b X w) =
      (fun (y : Fin M × Fin d → Ainf F) (w : InfinitePlace F) (p : Fin M × Fin d) => e (y p) w) ∘
        (fun X : Fin 1 → Fin M → Ainf F ⊗[F] E => cv (Ainf F) b (X 0)) := rfl
  have hr : 0 ≤ (Real.sqrt |(discr F : ℝ)|)⁻¹ := inv_nonneg.2 (Real.sqrt_nonneg _)
  have hcard : Fintype.card (Fin M × Fin d) = M * d := by
    simp only [Fintype.card_prod, Fintype.card_fin]
  rw [hcomp, ← Measure.map_map hΦ hemb.measurable, hcoord, ENNReal.ofReal_pow hr, ← hcard]
  exact InfPush.map_coord_pi laminf (fun x => e x) hem
    ((Real.sqrt |(discr F : ℝ)|)⁻¹).toNNReal hmap
