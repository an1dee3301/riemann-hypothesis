module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeftColumnsMulVecInjectiveOfRankEqCard
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.OpenClosedSequences
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Logic.Equiv.Defs

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL Matrix Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.leftColumns_mulVec_injective_of_rank_eq_card : ∀ (k m a b n : Type) [Field k] [Fintype m] [Fintype a] [Fintype b] [Fintype n] (e : a ⊕ b ≃ n) (x : Matrix m n k), x.rank = Fintype.card a → (∀ i j, x i (e (Sum.inr j)) = 0) → ∀ v : a → k, (x.submatrix id (fun i => e (Sum.inl i))) *ᵥ v = 0 → v = 0 := by
  first | exact @GlobalTheory.mulVec_firstCols_eq_zero_of_rank_eq_card | exact GlobalTheory.mulVec_firstCols_eq_zero_of_rank_eq_card | (intros; apply GlobalTheory.mulVec_firstCols_eq_zero_of_rank_eq_card <;> assumption)
