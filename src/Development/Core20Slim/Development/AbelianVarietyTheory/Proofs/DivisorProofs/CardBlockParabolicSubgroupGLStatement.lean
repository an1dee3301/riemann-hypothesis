module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardBlockParabolicSubgroupGL
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowBlockIndicatorFromLtIff
public import Init.Prelude
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.SetTheory.Cardinal.Finite

@[expose] public section

open NumberField UniqueFactorizationMonoid GlobalTheory.StdLoc

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_blockParabolicSubgroupGL : ∀ (R : Type) [CommRing R] [Finite R] (a d : ℕ), a ≤ d →
    Nat.card (blockPar R a d) = Nat.card (GL (Fin a) R) * Nat.card (GL (Fin (d - a)) R) * Nat.card R ^ (a * (d - a)) := by
  first | exact @GlobalTheory.StdLoc.card_blockPar | exact GlobalTheory.StdLoc.card_blockPar | (intros; apply GlobalTheory.StdLoc.card_blockPar <;> assumption)
