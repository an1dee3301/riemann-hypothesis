module

public import Mathlib
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteProductMultipliable
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicTupleProjectionsStatement
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CompletionIsLocalRingStatement
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelesLocallyCompactSecondCountableStatement
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import Init.BinderNameHint
public import Init.Classical
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.PropLemmas
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Notation.Indicator
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Notation.Support
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.WithAbs
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Countable.Defs
public import Mathlib.Basic.ENNReal.Action
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SProd
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Operations
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.MeasurableSpace.Pi
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Module
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.PiSystem
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.Order.Filter.Cofinite
public import Mathlib.Order.Filter.Defs
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.Tactic.Push
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Metrizable.Basic
public import Mathlib.Topology.Metrizable.Uniformity
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.EulerInt

theorem map_eq_prod {X Y ι : Type*} [MeasurableSpace X] [MeasurableSpace Y] [Fintype ι]
    {Z : ι → Type*} [∀ i, MeasurableSpace (Z i)]
    (I : Measure X) (μ₀ : Measure Y) (μ : ∀ i, Measure (Z i)) [SigmaFinite μ₀]
    [∀ i, SigmaFinite (μ i)] (c : ℝ≥0) (P : X → Y × ∀ i, Z i) (hP : Measurable P)
    (h : ∀ (A : Set Y) (B : ∀ i, Set (Z i)), MeasurableSet A → (∀ i, MeasurableSet (B i)) →
      I (P ⁻¹' (A ×ˢ Set.univ.pi B)) = (c : ℝ≥0∞) * (μ₀ A * ∏ i, μ i (B i))) :
    I.map P = (c • μ₀).prod (Measure.pi μ) := by
  symm
  refine Measure.prod_eq_generateFrom (C := {s | MeasurableSet s})
    (D := Set.univ.pi '' Set.univ.pi fun i => {s | MeasurableSet s})
    MeasurableSpace.generateFrom_measurableSet generateFrom_pi
    MeasurableSpace.isPiSystem_measurableSet isPiSystem_pi
    ((c • μ₀).toFiniteSpanningSetsIn)
    (Measure.FiniteSpanningSetsIn.pi fun i => (μ i).toFiniteSpanningSetsIn) ?_
  rintro s hs _ ⟨B, hB, rfl⟩
  have hB' : ∀ i, MeasurableSet (B i) := fun i => hB i (Set.mem_univ i)
  rw [Measure.map_apply hP (hs.prod (MeasurableSet.univ_pi hB')), h s B hs hB', Measure.pi_pi]
  rw [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, mul_assoc]

theorem integral_box {X Y ι : Type*} [MeasurableSpace X] [MeasurableSpace Y] [Fintype ι]
    {Z : ι → Type*} [∀ i, MeasurableSpace (Z i)]
    (I : Measure X) (μ₀ : Measure Y) (μ : ∀ i, Measure (Z i)) [SigmaFinite μ₀]
    [∀ i, SigmaFinite (μ i)] (c : ℝ≥0) (P : X → Y × ∀ i, Z i) (hP : Measurable P)
    (h : ∀ (A : Set Y) (B : ∀ i, Set (Z i)), MeasurableSet A → (∀ i, MeasurableSet (B i)) →
      I (P ⁻¹' (A ×ˢ Set.univ.pi B)) = (c : ℝ≥0∞) * (μ₀ A * ∏ i, μ i (B i)))
    (f₀ : Y → ℂ) (f : ∀ i, Z i → ℂ) (hf₀ : Integrable f₀ μ₀) (hf : ∀ i, Integrable (f i) (μ i)) :
    Integrable (fun x => f₀ (P x).1 * ∏ i, f i ((P x).2 i)) I ∧
      ∫ x, f₀ (P x).1 * ∏ i, f i ((P x).2 i) ∂I =
        (c : ℂ) * ((∫ y, f₀ y ∂μ₀) * ∏ i, ∫ z, f i z ∂(μ i)) := by
  have hmap := map_eq_prod I μ₀ μ c P hP h
  set g : (Y × ∀ i, Z i) → ℂ := fun z => f₀ z.1 * ∏ i, f i (z.2 i) with hg
  have hgi : Integrable g ((c • μ₀).prod (Measure.pi μ)) :=
    Integrable.mul_prod (hf₀.smul_measure_nnreal) (Integrable.fintype_prod_dep hf)
  rw [← hmap] at hgi
  refine ⟨(integrable_map_measure hgi.aestronglyMeasurable hP.aemeasurable).1 hgi, ?_⟩
  have h1 : ∫ x, g (P x) ∂I = ∫ z, g z ∂(I.map P) :=
    (integral_map hP.aemeasurable hgi.aestronglyMeasurable).symm
  have h2 : ∫ z, g z ∂((c • μ₀).prod (Measure.pi μ)) =
      (∫ y, f₀ y ∂(c • μ₀)) * ∫ z : (∀ i, Z i), ∏ i, f i (z i) ∂(Measure.pi μ) :=
    integral_prod_mul f₀ (fun z : (∀ i, Z i) => ∏ i, f i (z i))
  change ∫ x, g (P x) ∂I = _
  rw [h1, hmap, h2, integral_fintype_prod_eq_prod, integral_smul_nnreal_measure]
  simp [NNReal.smul_def, mul_assoc]

variable (F : Type) [Field F] [NumberField F]

theorem infinite_adeles_t2Space : T2Space (Ainf F) :=
  inferInstanceAs (T2Space (∀ v : InfinitePlace F, v.Completion))

theorem sc_ainf (h : SecondCountableTopology (AF F)) : SecondCountableTopology (Ainf F) := by
  have h' : SecondCountableTopology (Ainf F × Af F) := h
  have he : IsEmbedding (fun x : Ainf F => ((x, 0) : Ainf F × Af F)) :=
    isEmbedding_prodMkLeft 0
  exact he.secondCountableTopology

end GlobalTheory.CompanionTheory.SW.EulerInt

namespace GlobalTheory.CompanionTheory.SW.EulerInt

theorem finprod_eq_indicator {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {d n M : ℕ}
    (b : Module.Basis (Fin d) F E)
    (Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n → Fin M → Fv F v ⊗[F] E) → ℂ)
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (hS : ∀ v, v ∉ S → Φv v = (latV b v).indicator 1)
    (hae : ∀ X : (Fin n → Fin M → Af F ⊗[F] E), ∀ᶠ v in Filter.cofinite, projV v X ∈ latV b v)
    (X : Fin n → Fin M → AF F ⊗[F] E) :
    ∏ᶠ v, Φv v (projV v (projFin X)) =
      (intOff b S).indicator (fun Y => ∏ v ∈ S, Φv v (projV v (projFin Y))) X := by
  classical
  by_cases hX : X ∈ intOff b S
  · rw [Set.indicator_of_mem hX]
    refine finprod_eq_prod_of_mulSupport_subset _ ?_
    intro v hv
    by_contra hvS
    apply hv
    have hvS' : v ∉ S := by simpa using hvS
    simp only [hS v hvS']
    exact Set.indicator_of_mem (hX v hvS') _
  · rw [Set.indicator_of_notMem hX]
    have : ∃ v, v ∉ S ∧ projV v (projFin X) ∉ latV b v := by
      by_contra hne
      push Not at hne
      exact hX hne
    obtain ⟨v, hvS, hv⟩ := this
    refine finprod_eq_zero _ v ?_ ?_
    · simp only [hS v hvS]
      exact Set.indicator_of_notMem hv _
    · have hfin : {w | projV w (projFin X) ∉ latV b w}.Finite :=
        Filter.eventually_cofinite.1 (hae (projFin X))
      refine (hfin.union S.finite_toSet).subset ?_
      intro w hw
      by_contra hc
      simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not, Finset.mem_coe] at hc
      apply hw
      simp only [hS w hc.2]
      exact Set.indicator_of_mem hc.1 _

end GlobalTheory.CompanionTheory.SW.EulerInt

