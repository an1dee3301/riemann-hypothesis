module

public import Mathlib
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteProductMultipliable
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicTupleProjectionsStatement
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
public import Development.Core20Slim.GroundTheory.AutomorphicForms.ReductionMeasure
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SiegelWeilMeasureRankZero
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import GroundTheory.GlobalFields.Adele.Approximation
public import Init.Classical
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Notation.Indicator
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.ENNReal.BigOperators
public import Mathlib.Basic.ENNReal.Real
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Lattice.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Finsupp.SMul
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Operations
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.Basic
public import Mathlib.Order.Filter.Cofinite
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Notation
public import Mathlib.Order.SetNotation
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Free
public import Mathlib.RingTheory.Trace.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.Group
public import Mathlib.Topology.Algebra.InfiniteSum.SummationFilter
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.EulerBox

section Box

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem pureL_indicator_eq {d n M : ℕ} (b : Module.Basis (Fin d) F E)
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (φinf : (Fin n → Fin M → Ainf F ⊗[F] E) → ℝ≥0∞)
    (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → Fin M → Fv F v ⊗[F] E))
    (hS : ∀ v, v ∉ S → A v = latV b v) (X : Fin n → Fin M → AF F ⊗[F] E) :
    pureL b S φinf (fun v => (A v).indicator 1) X =
      {X : Fin n → Fin M → AF F ⊗[F] E | ∀ v, projV v (projFin X) ∈ A v}.indicator
        (fun X => φinf (projInf X)) X := by
  by_cases hX : ∀ v, projV v (projFin X) ∈ A v
  · have hI : X ∈ (intOff b S : Set (Fin n → Fin M → AF F ⊗[F] E)) := fun v hv => by
      rw [← hS v hv]; exact hX v
    have hB : X ∈ {X : Fin n → Fin M → AF F ⊗[F] E | ∀ v, projV v (projFin X) ∈ A v} := hX
    rw [pureL, Set.indicator_of_mem hI, Set.indicator_of_mem hB,
      Finset.prod_eq_one (fun v _ => Set.indicator_of_mem (hX v) _), mul_one]
  · have hB : X ∉ {X : Fin n → Fin M → AF F ⊗[F] E | ∀ v, projV v (projFin X) ∈ A v} := hX
    rw [Set.indicator_of_notMem hB]
    obtain ⟨v, hv⟩ := not_forall.1 hX
    by_cases hvS : v ∈ S
    · by_cases hI : X ∈ (intOff b S : Set (Fin n → Fin M → AF F ⊗[F] E))
      · rw [pureL, Set.indicator_of_mem hI,
          Finset.prod_eq_zero hvS (Set.indicator_of_notMem hv _), mul_zero]
      · rw [pureL, Set.indicator_of_notMem hI]
    · have hI : X ∉ (intOff b S : Set (Fin n → Fin M → AF F ⊗[F] E)) := fun h => hv (by
        rw [hS v hvS]; exact h v hvS)
      rw [pureL, Set.indicator_of_notMem hI]

theorem box_eq {d n M : ℕ} (b : Module.Basis (Fin d) F E) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → Fin M → Fv F v ⊗[F] E))
    (hS : ∀ v, v ∉ S → A v = latV b v) :
    {X : Fin n → Fin M → AF F ⊗[F] E | ∀ v, projV v (projFin X) ∈ A v} =
      intOff b S ∩ ⋂ v ∈ S, (fun X : Fin n → Fin M → AF F ⊗[F] E => projV v (projFin X)) ⁻¹' A v := by
  ext X
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage]
  constructor
  · intro h
    exact ⟨fun v hv => by rw [← hS v hv]; exact h v, fun v _ => h v⟩
  · rintro ⟨h1, h2⟩ v
    by_cases hv : v ∈ S
    · exact h2 v hv
    · rw [hS v hv]; exact h1 v hv

end Box

theorem measurableSet_box (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) {d : ℕ} (b : Module.Basis (Fin d) F E) (n M : ℕ)
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → Fin M → Fv F v ⊗[F] E))
    (hA : ∀ v, MeasurableSet (A v)) (hS : ∀ v, v ∉ S → A v = latV b v) :
    MeasurableSet {X : Fin n → Fin M → AF F ⊗[F] E | ∀ v, projV v (projFin X) ∈ A v} := by
  have : LocallyCompactSpace (AF F) := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  obtain ⟨-, -, -, -, -, -, -, hB, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hσ (AF F)
  have : BorelSpace (Fin n → Fin M → AF F ⊗[F] E) := hB n M
  obtain ⟨-, hFin, hV, -, hOff, -⟩ := GlobalTheory.T.adelic_tuple_projections F E σ hσ d b n M
  have hmeas : ∀ v, Measurable
      (fun X : Fin n → Fin M → AF F ⊗[F] E => projV v (projFin X)) := fun v => by
    have hc : Continuous (fun X : Fin n → Fin M → AF F ⊗[F] E => projV v (projFin X)) :=
      (hV v).comp hFin
    refine measurable_pi_iff.2 fun a => measurable_pi_iff.2 fun i => ?_
    have : BorelSpace (Fv F v ⊗[F] E) := ⟨rfl⟩
    exact (((continuous_apply i).comp (continuous_apply a)).comp hc).measurable
  rw [box_eq b S A hS]
  exact (hOff S).measurableSet.inter
    (Finset.measurableSet_biInter S fun v _ => hmeas v (hA v))

theorem euler_box : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (n M : ℕ) (I : Measure (Fin n → Fin M → AF F ⊗[F] E)) (c : ℝ≥0) (minf : Measure (Fin n → Fin M → Ainf F ⊗[F] E)) (m : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fin M → Fv F v ⊗[F] E)), IsEulerProd b I c minf m → ∀ (φinf : (Fin n → Fin M → Ainf F ⊗[F] E) → ℝ≥0∞) (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → Fin M → Fv F v ⊗[F] E)), Measurable φinf → (∀ v, MeasurableSet (A v)) → (∀ v, m v (A v) < ⊤) → (∀ᶠ v in Filter.cofinite, A v = latV b v) → Multipliable (fun v => (m v (A v)).toReal) ∧ ∫⁻ X in {X | ∀ v, projV v (projFin X) ∈ A v}, φinf (projInf X) ∂I = (c : ℝ≥0∞) * (∫⁻ X, φinf X ∂minf) * ENNReal.ofReal (∏' v, (m v (A v)).toReal) := by
  intro F E _ _ _ _ _ σ hσ d b n M I c minf m hE φinf A hφ hA hfin hcof
  classical
  obtain ⟨-, hsum, S₀, hS₀⟩ := hE
  have hfinite : {v | ¬ A v = latV b v}.Finite := Filter.eventually_cofinite.1 hcof
  set S : Finset (HeightOneSpectrum (𝓞 F)) := S₀ ∪ hfinite.toFinset with hSdef
  have hS : ∀ v, v ∉ S → A v = latV b v := fun v hv => by
    by_contra hne
    exact hv (Finset.mem_union_right _ (hfinite.mem_toFinset.2 hne))
  have hsumA : Summable (fun v => |(m v (A v)).toReal - 1|) :=
    hsum.congr_cofinite (hcof.mono fun v hv => by simp only [hv])
  obtain ⟨hmul, hsplit, -, hnn⟩ := GlobalTheory.CompanionTheory.SW.AbsTprod.abs_tprod _ _ hsumA
  refine ⟨hmul, ?_⟩
  have hbox := measurableSet_box F E σ hσ b n M S A hA hS
  have hform := hS₀ S Finset.subset_union_left φinf (fun v => (A v).indicator 1) hφ
    (fun v => measurable_one.indicator (hA v))
  have hlhs : ∫⁻ X, pureL b S φinf (fun v => (A v).indicator 1) X ∂I =
      ∫⁻ X in {X | ∀ v, projV v (projFin X) ∈ A v}, φinf (projInf X) ∂I := by
    simp_rw [pureL_indicator_eq b S φinf A hS]
    exact lintegral_indicator hbox _
  have hloc : ∀ v, ∫⁻ X, (A v).indicator 1 X ∂(m v) = ENNReal.ofReal (m v (A v)).toReal := fun v => by
    rw [lintegral_indicator_one (hA v), ENNReal.ofReal_toReal (hfin v).ne]
  have htail : ∏' v : {v // v ∉ S}, (m v.1 (latV b v.1)).toReal =
      ∏' v : {v // v ∉ S}, (m v.1 (A v.1)).toReal :=
    tprod_congr fun v => by rw [hS v.1 v.2]
  rw [hlhs] at hform
  rw [hform, htail, (hsplit S).2]
  simp_rw [hloc]
  rw [ENNReal.ofReal_mul (Finset.prod_nonneg fun v _ => ENNReal.toReal_nonneg),
    ENNReal.ofReal_prod_of_nonneg fun v _ => ENNReal.toReal_nonneg]
  ring

end GlobalTheory.CompanionTheory.SW.EulerBox
