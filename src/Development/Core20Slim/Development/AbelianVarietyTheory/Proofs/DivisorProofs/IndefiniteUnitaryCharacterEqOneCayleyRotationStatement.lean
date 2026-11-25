module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndefiniteUnitaryCharacterEqOneCayleyRotation
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
public import Formalism.LocalRingCardinality.DataTheta
public import Init.Core
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Matrix.Block
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Logic.Function.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open scoped Matrix
open Formalism.BasicNotions.TH
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.indefiniteUnitaryCharacter_eq_one_cayleyRotation : ∀ (R S : ℕ) (χ : Mat R S → ℂ),
    (∀ g h : Mat R S, gᴴ * Jm R S * g = Jm R S → hᴴ * Jm R S * h = Jm R S → χ (g * h) = χ g * χ h) →
    ContinuousOn χ {g : Mat R S | gᴴ * Jm R S * g = Jm R S} →
    (∀ g : Mat R S, gᴴ * Jm R S * g = Jm R S → χ g ≠ 0) →
    ∀ (i0 : Fin R) (j0 : Fin S) (x : ℝ),
      χ (Matrix.fromBlocks (Matrix.diagonal (Function.update 1 i0 ((1 + 2 * Complex.I * x) / (1 - 2 * Complex.I * x)))) 0 0
        (Matrix.diagonal (Function.update 1 j0 ((1 - 2 * Complex.I * x) / (1 + 2 * Complex.I * x))))) = 1 := by
  first | exact @GlobalTheory.UnitaryCharRot.char_eq_one_rot | exact GlobalTheory.UnitaryCharRot.char_eq_one_rot | (intros; apply GlobalTheory.UnitaryCharRot.char_eq_one_rot <;> assumption)
