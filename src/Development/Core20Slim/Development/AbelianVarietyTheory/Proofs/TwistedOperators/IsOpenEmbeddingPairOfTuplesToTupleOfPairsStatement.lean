module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsOpenEmbeddingPairOfTuplesToTupleOfPairs
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.MulVecCEApply
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
public import Init.Prelude
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Induced

@[expose] public section

open MeasureTheory Topology Matrix NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.ModuLR
open scoped NNReal ENNReal TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isOpenEmbedding_pairOfTuplesToTupleOfPairs : ∀ (κ X Y : Type) [Fintype κ] [AddCommGroup X] [TopologicalSpace X] [AddCommGroup Y] [TopologicalSpace Y], IsOpenEmbedding (zipHom κ X Y) := by
  first | exact @GlobalTheory.ModuLR.zipHom_isOpenEmbedding | exact GlobalTheory.ModuLR.zipHom_isOpenEmbedding | (intros; apply GlobalTheory.ModuLR.zipHom_isOpenEmbedding <;> assumption)
