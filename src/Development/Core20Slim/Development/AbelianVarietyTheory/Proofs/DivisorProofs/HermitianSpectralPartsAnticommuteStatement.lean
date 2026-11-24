module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianSpectralPartsAnticommute
public import Init.Core
public import Init.Prelude
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Hermitian

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_spectral_projections_anticommute : ∀ (n : Type) [Fintype n] [DecidableEq n] (Y J : Matrix n n ℂ), Y.IsHermitian → J * Y = -(Y * J) → ∃ (s : Finset ℝ) (N E : ℝ → Matrix n n ℂ), Y = ∑ ν ∈ s, (ν : ℂ) • N ν ∧ (∀ ν, (N ν).IsHermitian ∧ (E ν).IsHermitian ∧ Y * N ν = (ν : ℂ) • E ν ∧ N ν * Y = (ν : ℂ) • E ν ∧ Y * E ν = (ν : ℂ) • N ν ∧ E ν * Y = (ν : ℂ) • N ν ∧ J * N ν = -(N ν * J) ∧ J * E ν = E ν * J) ∧ ∀ ν ν', E ν * E ν' = E ν' * E ν := by
  first | exact @GlobalTheory.hermitian_spectral_parts_anticommute | exact GlobalTheory.hermitian_spectral_parts_anticommute | (intros; apply GlobalTheory.hermitian_spectral_parts_anticommute <;> assumption)
