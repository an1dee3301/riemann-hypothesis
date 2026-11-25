module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianBlockSolutionExists
public import Development.Core20Slim.Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.EisCellsDefs
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsBlockMatrixTwoByTwoFinEq
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

@[expose] public section

open scoped Matrix
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions.EC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_block_solution_exists : ∀ {K : Type} [Field K] (σ : K →+* K), (∀ x, σ (σ x) = x) → ∀ {n r : ℕ}, r ≤ n → ∀ (c : Matrix (Fin r) (Fin n) K) (a C D : Matrix (Fin n) (Fin n) K) (T : Matrix (Fin n) (Fin r) K) (L : Matrix (Fin r) (Fin n) K), IsCompl c a → C = T * c → L * T = 1 → C * cT σ D = D * cT σ C → ∃ b : Matrix (Fin r) (Fin r) K, cT σ b = b ∧ C * a⁻¹ * (1 - eId K n r - extB b) + D * cT σ a * eId K n r = 0 := by
  first | exact @GlobalTheory.CompanionTheory.BruhatCell.exists_hermitian_lowerLeft | exact GlobalTheory.CompanionTheory.BruhatCell.exists_hermitian_lowerLeft | (intros; apply GlobalTheory.CompanionTheory.BruhatCell.exists_hermitian_lowerLeft <;> assumption)
