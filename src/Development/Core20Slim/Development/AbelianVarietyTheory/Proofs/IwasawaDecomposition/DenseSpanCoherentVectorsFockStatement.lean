module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DenseSpanCoherentVectorsFock
public import Formalism.LocalRingCardinality.DataTheta
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.OscActMonomialOfUnique
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsNegBaseY
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Set.Operations
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH GlobalTheory.Mem.Osc GlobalTheory.OscGauss Matrix
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dense_span_coherent_vectors_fock : ∀ (P Q : ℕ) (F : Fock (Ix P Q)) (e : (Ix P Q → ℂ) → F.H), (∀ x, HasCoeff F (e x) (expPS (gaussPoly (0 : Matrix (Fin P) (Fin Q) ℂ) x))) → Dense (Submodule.span ℂ (Set.range e) : Set F.H) := by
  first | exact @GlobalTheory.dense_span_coherent | exact GlobalTheory.dense_span_coherent | (intros; apply GlobalTheory.dense_span_coherent <;> assumption)
