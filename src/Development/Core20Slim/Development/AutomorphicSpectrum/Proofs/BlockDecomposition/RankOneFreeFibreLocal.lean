module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HypOneZeroZero
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalGramFiberRankOneSetFormula
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CompletionIsLocalRingStatement
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TrMMemFramesEIff
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import Init.Core
public import Init.Data.Fin.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Finsupp.SMul
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.MeasurableSpace.Embedding
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.MeasureTheory.OuterMeasure.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.BooleanAlgebra.Set
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.Artinian.Defs
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Free
public import Mathlib.RingTheory.Trace.Defs
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Support
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.ContinuousOn
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free

namespace GlobalTheory.CompanionTheory.WeilSiegel.Free.LengthFibre

open GlobalTheory.CompanionTheory.SW.FibreRatio

theorem isFibreFamily_field {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E}
    (R : Type) [Field R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R]
    (hloc : IsLocR R) (h : IsCMExt F E σ) {d : ℕ} (b : Module.Basis (Fin d) F E) (lam : Measure R)
    (hlam : lam.IsAddHaarMeasure)
    (m : HermR R σ 1 → Measure (Fin 1 → Fin M → R ⊗[F] E))
    (hm : IsGramFibFree R σ J 1 (coordW R b lam 1 M) (coordHerm R σ b lam 1) m) :
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily (coordW R b lam 1 M)
      (fun X : Fin 1 → Fin M → R ⊗[F] E =>
        algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) (gramR R σ J X 0 0)) id
      {X : Fin 1 → Fin M → R ⊗[F] E | LinearIndependent (R ⊗[F] E) X} lam Set.univ
      (fun s => m (hermScal R σ s)) := by
  obtain ⟨h1, h2, h3, h4, -⟩ := id hloc
  haveI := h1
  haveI := h2
  haveI := h3
  haveI := h4
  obtain ⟨-, -, -, hT2, -, htr, -, hBor, -, hgr⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ h R
  haveI := hT2
  haveI : BorelSpace (HermR R σ 1) := ⟨rfl⟩
  obtain ⟨hc1, hc2, hc3⟩ := hm
  have hcs : Continuous (hermScal R σ (F := F) (E := E)) := continuous_hermScal R
  have hcq : Continuous (qS R σ (F := F) (E := E)) := continuous_qS R htr
  have hmap : coordHerm R σ b lam 1 = lam.map (hermScal R σ) := by
    refine Measure.ext fun A hA => ?_
    rw [Measure.map_apply hcs.measurable hA, ← coordHerm_qS R h htr b lam (hcs.measurable hA)]
    congr 1
    ext S
    show S ∈ A ↔ hermScal R σ (qS R σ S) ∈ A
    rw [hermScal_qS R h S]
  have hemb : MeasurableEmbedding (hermScal R σ (F := F) (E := E)) :=
    (Homeomorph.mk ⟨hermScal R σ, qS R σ, qS_hermScal R h, hermScal_qS R h⟩ hcs hcq).measurableEmbedding
  refine ⟨fun s => ?_, fun φ hφ => ?_, fun φ hφc hφs hφU => ?_⟩
  · refine measure_mono_null (Set.compl_subset_compl.mpr ?_) (hc1 (hermScal R σ s))
    rintro X ⟨hX, hXU⟩
    refine ⟨?_, hXU⟩
    have e : gramR R σ J X = ((hermScal R σ s : HermR R σ 1) : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) := hX
    show algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) (gramR R σ J X 0 0) = s
    rw [e]
    exact qS_hermScal R h s
  · rw [hc2 φ hφ, hmap, hemb.lintegral_map]
  · obtain ⟨ha, hb⟩ := hc3 φ hφc hφs hφU
    exact ⟨fun s _ => ha _ (Set.mem_univ _),
      (hb.comp hcs.continuousOn (fun _ _ => Set.mem_univ _))⟩

end GlobalTheory.CompanionTheory.WeilSiegel.Free.LengthFibre

namespace GlobalTheory.CompanionTheory.WeilSiegel.Free

theorem isFibreFamily_length : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v)), IsStdV v lam → ∀ (m : HermR (Fv F v) σ 1 → Measure (Fin 1 → Fin M → Fv F v ⊗[F] E)), IsGramFibFree (Fv F v) σ J 1 (coordW (Fv F v) b lam 1 M) (coordHerm (Fv F v) σ b lam 1) m → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily (coordW (Fv F v) b lam 1 M) (fun X : Fin 1 → Fin M → Fv F v ⊗[F] E => algebraMap F (Fv F v) (1 / 2) * Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (gramR (Fv F v) σ J X 0 0)) id {X : Fin 1 → Fin M → Fv F v ⊗[F] E | LinearIndependent (Fv F v ⊗[F] E) X} lam Set.univ (fun s => m (hermScal (Fv F v) σ s)) := by
  intro F E _ _ _ _ _ σ hσ M J hJ d b v lam hlam m hm
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  exact LengthFibre.isFibreFamily_field (Fv F v) (GlobalTheory.T.completion_is_local_ring F v) hσ b lam hlam.1 m hm

end GlobalTheory.CompanionTheory.WeilSiegel.Free
