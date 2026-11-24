module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SpanRangeComplementTransform
public import Development.Core20Slim.Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.EisCellsDefs
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsBlockMatrixTwoByTwoFinEq
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Set.Operations
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Span.Defs

@[expose] public section

open scoped Matrix
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions.EC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.span_range_complement_transform : ∀ {K : Type} [Field K] {n r : ℕ}, r ≤ n → ∀ (c : Matrix (Fin r) (Fin n) K) (a p : Matrix (Fin n) (Fin n) K), IsCompl c a → IsUnit p.det → Submodule.span K (Set.range (p * -(eId K n r * a))) = Submodule.span K (Set.range c) := by
  first | exact @GlobalTheory.CompanionTheory.BruhatCell.span_range_lowerLeft | exact GlobalTheory.CompanionTheory.BruhatCell.span_range_lowerLeft | (intros; apply GlobalTheory.CompanionTheory.BruhatCell.span_range_lowerLeft <;> assumption)
