module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsOpenEmbeddingFiniteAdeleOfSPartAndIntegralPart
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.MulVecCEApply
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Pi
public import Mathlib.Algebra.Ring.Prod
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open MeasureTheory Topology Matrix NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.ModuLR
open scoped NNReal ENNReal TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isOpenEmbedding_finiteAdeleOfSPartAndIntegralPart : ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))), IsOpenEmbedding (jS F S) := by
  first | exact @GlobalTheory.ModuLR.isOpenEmbedding_jS | exact GlobalTheory.ModuLR.isOpenEmbedding_jS | (intros; apply GlobalTheory.ModuLR.isOpenEmbedding_jS <;> assumption)
