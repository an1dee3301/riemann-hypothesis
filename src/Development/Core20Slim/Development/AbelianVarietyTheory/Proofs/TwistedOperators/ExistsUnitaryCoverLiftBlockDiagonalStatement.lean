module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitaryCoverLiftBlockDiagonal
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousExptPY
public import Formalism.LocalRingCardinality.DataTheta
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Matrix.Block
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.UnitaryGroup

@[expose] public section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitaryCover_lift_blockDiagonal : ∀ (p q : ℕ) (T : GrpData p q), ∀ U ∈ Matrix.unitaryGroup (Fin p) ℂ, ∀ V ∈ Matrix.unitaryGroup (Fin q) ℂ, ∃ k ∈ T.Kset, matG T k = Matrix.fromBlocks U 0 0 V := by
  first | exact @GlobalTheory.PolarU.exists_lift_blocks | exact GlobalTheory.PolarU.exists_lift_blocks | (intros; apply GlobalTheory.PolarU.exists_lift_blocks <;> assumption)
