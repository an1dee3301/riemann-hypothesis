module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormPowLeConstMulOneAddSumAbsBasisCoordPow
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsContOnOfLocal
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdeleJoinZero
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.LinearAlgebra.Basis.Defs

@[expose] public section

open IsDedekindDomain NumberField
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_pow_le_const_mul_one_add_sum_abs_basisCoord_pow : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (ι : Type) [Fintype ι] (b : Module.Basis ι ℝ E) (i : ℕ),
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x : E, ‖x‖ ^ i ≤ K * (1 + ∑ c, |b.coord c x| ^ i) := by
  first | exact @GlobalTheory.norm_pow_le_const_mul_one_add_sum_abs_coord_pow | exact GlobalTheory.norm_pow_le_const_mul_one_add_sum_abs_coord_pow | (intros; apply GlobalTheory.norm_pow_le_const_mul_one_add_sum_abs_coord_pow <;> assumption)
