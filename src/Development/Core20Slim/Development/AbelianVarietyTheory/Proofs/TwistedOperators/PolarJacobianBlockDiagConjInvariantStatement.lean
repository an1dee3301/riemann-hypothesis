module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.PolarJacobianBlockDiagConjInvariant
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousExptPY
public import Formalism.LocalRingCardinality.DataTheta
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Defs

@[expose] public section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarJacobian_blockDiag_conj_invariant : ∀ (p q : ℕ) (k k' Y : Mat p q), k * k' = 1 → IsKC k → IsKC k' → polJ (k * Y * k') = polJ Y := by
  first | exact @GlobalTheory.PolarU.Conj.polJ_conj | exact GlobalTheory.PolarU.Conj.polJ_conj | (intros; apply GlobalTheory.PolarU.Conj.polJ_conj <;> assumption)
