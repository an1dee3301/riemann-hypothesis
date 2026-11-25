module

public import Mathlib
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.SiegelOneDescent.Descend2
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.Core20Slim.Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.AdelicHomeomorphisms.IsTopologicalGroupG2
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.ConvGrOf
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.DictInf
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.IsEpCont
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.Core20Slim.GroundTheory.AutomorphicForms.ReductionHeight
public import Development.Core20Slim.GroundTheory.GlobalFields.Adele.BaseChange.AdeleEquiv
public import Development.Core20Slim.GroundTheory.GlobalFields.SemilocalAlgebras.InfiniteAdele
public import Development.Core20Slim.GroundTheory.IdeleRoots.TorusPowers.HeckeTensor
public import Init.Core
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Pi
public import Mathlib.Algebra.Ring.Prod
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.WithAbs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.Normed.Ring.WithAbs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.FieldTheory.Separable
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
public import Mathlib.NumberTheory.NumberField.Completion.LiesOverInstances
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Unramified.Basic
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.DenseEmbedding
public import Mathlib.Topology.EMetricSpace.Defs
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.Isometry
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

open NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open scoped NumberField.AdeleRing NumberField.LiesOver TensorProduct
open PositivityTheory.RgEis PositivityTheory.RgEis.So
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl

namespace GlobalTheory.CompanionTheory.RgEisSo

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem embedding_algebraMap_of_totallyReal (hF : IsTotallyReal F) (w : InfinitePlace E) (x : F) :
    w.embedding (algebraMap F E x) = (w.comap (algebraMap F E)).embedding x := by
  have hreal : ComplexEmbedding.IsReal (w.comap (algebraMap F E)).embedding :=
    InfinitePlace.isReal_iff.1 (IsTotallyReal.isReal _)
  have h : InfinitePlace.mk (w.embedding.comp (algebraMap F E)) =
      InfinitePlace.mk (w.comap (algebraMap F E)).embedding := by
    rw [InfinitePlace.mk_embedding, ← InfinitePlace.comap_mk, InfinitePlace.mk_embedding]
  rcases InfinitePlace.mk_eq_iff.1 h with h | h
  · exact congrArg (fun f : F →+* ℂ => f x) h
  · have h' : w.embedding.comp (algebraMap F E) = (w.comap (algebraMap F E)).embedding := by
      have h2 : ComplexEmbedding.conjugate (ComplexEmbedding.conjugate (w.embedding.comp (algebraMap F E))) =
          w.embedding.comp (algebraMap F E) := star_star _
      rw [← h2, h]
      exact ComplexEmbedding.isReal_iff.1 hreal
    exact congrArg (fun f : F →+* ℂ => f x) h'

theorem extensionEmbedding_algebraMap_of_totallyReal (hF : IsTotallyReal F) (w : InfinitePlace E)
    (z : (w.comap (algebraMap F E)).Completion) :
    extensionEmbedding w (algebraMap (w.comap (algebraMap F E)).Completion w.Completion z) =
      extensionEmbedding (w.comap (algebraMap F E)) z := by
  rw [AbsoluteValue.Completion.algebraMap_eq_of_liesOver (w.comap (algebraMap F E)).1 w.1]
  have h := (denseRange_coe (v := w.comap (algebraMap F E))).equalizer
    (g := fun z => extensionEmbedding w (AbsoluteValue.Completion.map (w.comap (algebraMap F E)).1 w.1 z))
    (h := fun z => extensionEmbedding (w.comap (algebraMap F E)) z)
    ((isometry_extensionEmbedding w).continuous.comp (AbsoluteValue.Completion.continuous_map _ _))
    (isometry_extensionEmbedding _).continuous (funext fun k => ?_)
  · exact congrFun h z
  · have e := LiesOver.completionMap_coe (v := w.comap (algebraMap F E)) (w := w) k
    show extensionEmbedding w (AbsoluteValue.Completion.map (w.comap (algebraMap F E)).1 w.1 (k : (w.comap (algebraMap F E)).Completion)) =
      extensionEmbedding (w.comap (algebraMap F E)) (k : (w.comap (algebraMap F E)).Completion)
    rw [e, extensionEmbedding_coe, extensionEmbedding_coe]
    exact embedding_algebraMap_of_totallyReal hF w _

theorem phi_nuCM (σ : E →ₐ[F] E) (χ : Chr F E) (hF : IsTotallyReal F) (w : InfinitePlace E) (x : 𝔸[F]) :
    (adCM σ χ).φ w (nuCM F E x) = (adStd F).φ (w.comap (algebraMap F E)) x := by
  have h : eqv F E (nuCM F E x) = GroundTheory.Global.AdeleBaseChange.adeleMap F E x :=
    GroundTheory.BlockD.ThmBHecke.adeleEquiv_algebraMap x
  show extensionEmbedding w (GroundTheory.Automorphic.Reduction.infEval w (eqv F E (nuCM F E x))) =
    extensionEmbedding _ (GroundTheory.Automorphic.Reduction.infEval _ x)
  rw [h]
  exact extensionEmbedding_algebraMap_of_totallyReal hF w _

end GlobalTheory.CompanionTheory.RgEisSo

namespace GlobalTheory.CompanionTheory.RgEisSo

theorem bInf : BInf := by
  intro F E _ _ _ _ _ σ χ c hcm _ _ _
  haveI : IsTotallyReal F := hcm.1
  refine ⟨fun w => ⟨w.comap (algebraMap F E), fun x => phi_nuCM σ χ hcm.1 w x⟩, fun v => ?_⟩
  obtain ⟨w, rfl⟩ := InfinitePlace.comap_surjective (k := F) (K := E) v
  exact ⟨w, fun x => phi_nuCM σ χ hcm.1 w x⟩

end GlobalTheory.CompanionTheory.RgEisSo
