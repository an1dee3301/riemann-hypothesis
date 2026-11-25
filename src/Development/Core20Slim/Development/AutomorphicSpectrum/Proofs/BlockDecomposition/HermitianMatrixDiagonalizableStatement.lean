module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianMatrixDiagonalizable
public import Development.Core20Slim.Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.LocalDefs
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResAlgSplitTwo
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FixedNondeg
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedQuotientCardStatement
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
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

@[expose] public section

open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.SiegLoc Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_matrix_diagonalizable : ∀ (R : Type) [CommRing R] (σ : R →+* R) (ϖ : R) (q : ℕ) (ε : ℤ), IsUnrQuad R σ ϖ q ε → ∀ (n : ℕ) (h : Matrix (Fin n) (Fin n) R), cT σ h = h → ∃ (g g' : Matrix (Fin n) (Fin n) R) (d : Fin n → R), g * g' = 1 ∧ g' * g = 1 ∧ (∀ i, σ (d i) = d i) ∧ cT σ g * h * g = Matrix.diagonal d := by
  first | exact @GlobalTheory.CompanionTheory.HermDiag.herm_diag | exact GlobalTheory.CompanionTheory.HermDiag.herm_diag | (intros; apply GlobalTheory.CompanionTheory.HermDiag.herm_diag <;> assumption)
