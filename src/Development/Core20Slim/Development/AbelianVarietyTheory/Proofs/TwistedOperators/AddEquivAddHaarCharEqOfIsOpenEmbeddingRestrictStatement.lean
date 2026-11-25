module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.AddEquivAddHaarCharEqOfIsOpenEmbeddingRestrict
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.MulVecCEApply
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
public import Init.Prelude
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.Haar.MulEquivHaarChar
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Separation.Hausdorff

@[expose] public section

open MeasureTheory Topology Matrix NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.ModuLR
open scoped NNReal ENNReal TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.addEquivAddHaarChar_eq_of_isOpenEmbedding_restrict : ∀ (G G' : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [LocallyCompactSpace G] [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [AddCommGroup G'] [TopologicalSpace G'] [IsTopologicalAddGroup G'] [LocallyCompactSpace G'] [T2Space G'] [SecondCountableTopology G'] [MeasurableSpace G'] [BorelSpace G'] (j : G' →+ G), IsOpenEmbedding j → ∀ (e : G ≃ₜ+ G) (e' : G' ≃ₜ+ G'), (∀ x, e (j x) = j (e' x)) → addEquivAddHaarChar e = addEquivAddHaarChar e' := by
  first | exact @GlobalTheory.HaarOpenEmb.addEquivAddHaarChar_eq_of_isOpenEmbedding | exact GlobalTheory.HaarOpenEmb.addEquivAddHaarChar_eq_of_isOpenEmbedding | (intros; apply GlobalTheory.HaarOpenEmb.addEquivAddHaarChar_eq_of_isOpenEmbedding <;> assumption)
