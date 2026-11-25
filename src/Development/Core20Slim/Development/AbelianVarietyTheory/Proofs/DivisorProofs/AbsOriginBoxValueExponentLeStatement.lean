module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsOriginBoxValueExponentLe
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasurableSetSetOfLe
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.Order.Lattice
public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
public import Mathlib.Topology.Defs.Basic

@[expose] public section

open MeasureTheory ValuativeRel Matrix
open GlobalTheory.OriginBox GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abs_originBoxValueExponent_le : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (G : Grid k), 1 ≤ G.s → ∀ (a a' : ℤ) (N : ℕ), (∀ i j, i ≤ G.m → j ≤ G.m → G.rank (i, j) ≤ N) → |expo G a a'| ≤ 8 * ((G.m : ℤ) ^ 3 * (N : ℤ) ^ 2 * (|a| + |a'|)) := by
  first | exact @GlobalTheory.OriginBox.abs_expo_le | exact GlobalTheory.OriginBox.abs_expo_le | (intros; apply GlobalTheory.OriginBox.abs_expo_le <;> assumption)
