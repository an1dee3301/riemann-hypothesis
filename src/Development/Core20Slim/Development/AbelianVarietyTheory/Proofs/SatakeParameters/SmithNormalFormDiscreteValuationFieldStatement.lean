module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmithNormalFormDiscreteValuationField
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.SatakeParameters.SelfDualOne
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeModelVacuumTranslateClassesIndependent
public import Formalism.SatakeDualWeyl.StatementF
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.WithOne.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Topology.Algebra.Valued.ValuationTopology

@[expose] public section

open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smithNormalForm_discreteValuationField : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (m n : ℕ) (M : Matrix (Fin m) (Fin n) L),
    ∃ (P P' : Matrix (Fin m) (Fin m) L) (Q Q' : Matrix (Fin n) (Fin n) L) (d : Fin m → L),
      (∀ i j, P i j ∈ Formalism.UG.intL L) ∧ (∀ i j, P' i j ∈ Formalism.UG.intL L) ∧
      (∀ i j, Q i j ∈ Formalism.UG.intL L) ∧ (∀ i j, Q' i j ∈ Formalism.UG.intL L) ∧ P * P' = 1 ∧ Q * Q' = 1 ∧
      M = P * Matrix.of (fun (j : Fin m) (k : Fin n) => if (k : ℕ) = (j : ℕ) then d j else 0) * Q := by
  first | exact @GlobalTheory.SmithValued.smith_valued | exact GlobalTheory.SmithValued.smith_valued | (intros; apply GlobalTheory.SmithValued.smith_valued <;> assumption)
