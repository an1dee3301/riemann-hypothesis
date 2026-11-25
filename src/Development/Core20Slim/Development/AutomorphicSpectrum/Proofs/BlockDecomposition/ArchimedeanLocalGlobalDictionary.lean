module

public import Mathlib
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.DictInf
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.ConvGrOf
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.IsEpCont
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.Core20Slim.GroundTheory.GlobalFields.Adele.BaseChange.AdeleEquiv
public import Development.Core20Slim.GroundTheory.GlobalFields.SemilocalAlgebras.Infinite
public import Development.Core20Slim.GroundTheory.GlobalFields.SemilocalAlgebras.InfiniteAdele
public import Development.Core20Slim.GroundTheory.IdeleRoots.TorusPowers.HeckeTensor
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Algebra.Ring.Hom.Defs
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
public import Mathlib.Data.NNRat.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Rat.Init
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
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.Algebra.Algebra
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.DenseEmbedding
public import Mathlib.Topology.EMetricSpace.Defs
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.Isometry
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GlobalTheory.CompanionTheory.RgEis

open scoped TensorProduct NumberField.AdeleRing NumberField.LiesOver
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels PositivityTheory.RgEis GroundTheory.Automorphic.Reduction

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem embedding_comp [IsTotallyReal F] (w : InfinitePlace E) :
    w.embedding.comp (algebraMap F E) = (w.comap (algebraMap F E)).embedding := by
  conv_rhs => rw [← w.mk_embedding, InfinitePlace.comap_mk]
  exact (InfinitePlace.embedding_mk_eq_of_isReal
    (InfinitePlace.isReal_mk_iff.1 (IsTotallyReal.isReal _))).symm

def embOf [IsTotallyReal F] (w : InfinitePlace E) : EmbOver E (w.comap (algebraMap F E)) :=
  ⟨w.embedding, embedding_comp w⟩

theorem conj_ext [IsTotallyReal F] (w : InfinitePlace F) (a : w.Completion) :
    starRingEnd ℂ (InfinitePlace.Completion.extensionEmbedding w a) =
      InfinitePlace.Completion.extensionEmbedding w a := by
  have hr : w.IsReal := IsTotallyReal.isReal w
  rw [← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hr, Complex.conj_ofReal]

theorem ext_algebraMap [IsTotallyReal F] (w : InfinitePlace E) (a : (w.comap (algebraMap F E)).Completion) :
    InfinitePlace.Completion.extensionEmbedding w (algebraMap _ w.Completion a) =
      InfinitePlace.Completion.extensionEmbedding (w.comap (algebraMap F E)) a := by
  have c1 : Continuous fun a : (w.comap (algebraMap F E)).Completion =>
      InfinitePlace.Completion.extensionEmbedding w (algebraMap _ w.Completion a) :=
    (InfinitePlace.Completion.isometry_extensionEmbedding w).continuous.comp
      (continuous_algebraMap _ _)
  have c2 := (InfinitePlace.Completion.isometry_extensionEmbedding (w.comap (algebraMap F E))).continuous
  refine congrFun ((InfinitePlace.Completion.denseRange_coe (w.comap (algebraMap F E))).equalizer c1 c2
    (funext fun x => ?_)) a
  obtain ⟨k, rfl⟩ := (WithAbs.equiv (w.comap (algebraMap F E)).1).symm.surjective x
  simp only [Function.comp_apply]
  have hk : ((WithAbs.equiv (w.comap (algebraMap F E)).1).symm k : (w.comap (algebraMap F E)).Completion) = algebraMap F (w.comap (algebraMap F E)).Completion k := by
    rw [InfinitePlace.Completion.algebraMap_apply]
    rfl
  rw [hk]
  change InfinitePlace.Completion.extensionEmbedding w (algebraMap _ w.Completion
      (algebraMap F (w.comap (algebraMap F E)).Completion k)) =
    InfinitePlace.Completion.extensionEmbedding (w.comap (algebraMap F E))
      (algebraMap F (w.comap (algebraMap F E)).Completion k)
  rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply F E]
  have e1 : InfinitePlace.Completion.extensionEmbedding w (algebraMap E w.Completion (algebraMap F E k)) =
      w.embedding (algebraMap F E k) :=
    by simpa [InfinitePlace.Completion.algebraMap_apply] using
      InfinitePlace.Completion.extensionEmbedding_coe w ((WithAbs.equiv w.1).symm (algebraMap F E k))
  have e2 : InfinitePlace.Completion.extensionEmbedding (w.comap (algebraMap F E))
      (algebraMap F (w.comap (algebraMap F E)).Completion k) = (w.comap (algebraMap F E)).embedding k :=
    by simpa [InfinitePlace.Completion.algebraMap_apply] using
      InfinitePlace.Completion.extensionEmbedding_coe _ ((WithAbs.equiv (w.comap (algebraMap F E)).1).symm k)
  rw [e1, e2]
  exact RingHom.congr_fun (embedding_comp w) k

theorem phi_eqv [IsTotallyReal F] (w : InfinitePlace E) (z : AE F E) :
    (adStd E).φ w (eqv F E z) = piInf (embOf w) z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul a x =>
    have e : eqv F E (a ⊗ₜ x) = algebraMap E 𝔸[E] x * GroundTheory.Global.AdeleBaseChange.adeleMap F E a :=
      GroundTheory.BlockD.ThmBHecke.adeleEquiv_tmul a x
    rw [e, map_mul]
    change _ * InfinitePlace.Completion.extensionEmbedding w (algebraMap _ w.Completion (a.1 (w.comap (algebraMap F E)))) =
      InfinitePlace.Completion.extensionEmbedding (w.comap (algebraMap F E)) (a.1 (w.comap (algebraMap F E))) * w.embedding x
    rw [ext_algebraMap, mul_comm]
    congr 1
    change InfinitePlace.Completion.extensionEmbedding w ((algebraMap E 𝔸[E] x).1 w) = w.embedding x
    rw [AdeleRing.algebraMap_fst_apply]
    exact InfinitePlace.Completion.extensionEmbedding_coe w ((WithAbs.equiv w.1).symm x)

theorem piInf_cA [IsTotallyReal F] {σ : E →ₐ[F] E} (h : IsCMExt F E σ) {w : InfinitePlace F} (τ : EmbOver E w)
    (z : AE F E) : piInf τ (cA σ z) = starRingEnd ℂ (piInf τ z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul a x =>
    change InfinitePlace.Completion.extensionEmbedding w (a.1 w) * τ.1 (σ x) =
      starRingEnd ℂ (InfinitePlace.Completion.extensionEmbedding w (a.1 w) * τ.1 x)
    rw [map_mul, conj_ext, h.2.2.2]
    rfl

theorem place_cases [IsTotallyReal F] {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (w' : InfinitePlace E)
    {w : InfinitePlace F} (hv : w'.comap (algebraMap F E) = w) (τ : EmbOver E w) :
    (∀ z, piInf τ z = (adStd E).φ w' (eqv F E z)) ∨
      ∀ z, piInf τ z = starRingEnd ℂ ((adStd E).φ w' (eqv F E z)) := by
  subst hv
  rcases infEmb_eq_or_conj h (embOf w') τ with e | e
  · refine Or.inl fun z => ?_
    rw [phi_eqv]
    exact RingHom.congr_fun e (compInf F E _ z)
  · refine Or.inr fun z => ?_
    rw [phi_eqv]
    exact RingHom.congr_fun e (compInf F E _ z)

theorem dictInf : DictInf := by
  intro F E _ _ _ _ _ σ h
  have := h.1
  refine ⟨fun w z => ?_, fun τ => ⟨fun w => ?_, fun w' => ⟨w'.comap (algebraMap F E), place_cases h w' rfl _⟩⟩⟩
  · rw [phi_eqv, phi_eqv]
    exact piInf_cA h _ z
  · refine ⟨InfinitePlace.mk (τ w).1, place_cases h _ ?_ (τ w)⟩
    rw [InfinitePlace.comap_mk, (τ w).2, InfinitePlace.mk_embedding]

end GlobalTheory.CompanionTheory.RgEis
