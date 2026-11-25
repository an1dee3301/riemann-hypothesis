module

public import Mathlib
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TotallyRealContinuousEmbeddingInfiniteAdeles
public import Init.Core
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.WithAbs
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.totally_real_continuous_embedding_infinite_adeles : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → (∃ θ : ℝ →+* InfiniteAdeleRing F, Continuous θ) ∧ ∀ θ : ℝ →+* InfiniteAdeleRing F, Continuous θ → ∀ (t : ℝ) (w : InfinitePlace F), ‖θ t w‖ = |t| := by
  first | exact @GlobalTheory.CompanionTheory.AdelicRealLine.exists_continuous_real_embedding | exact GlobalTheory.CompanionTheory.AdelicRealLine.exists_continuous_real_embedding | (intros; apply GlobalTheory.CompanionTheory.AdelicRealLine.exists_continuous_real_embedding <;> assumption)
