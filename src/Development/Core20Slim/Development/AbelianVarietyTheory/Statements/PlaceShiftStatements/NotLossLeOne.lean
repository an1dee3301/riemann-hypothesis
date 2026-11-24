module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ValBasic
public import Formalism.QuotientMetricDivisors.Statement
public import Init.Classical
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
public import Mathlib.Algebra.GroupWithZero.Units.Lemmas
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Int.Cast.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.RingTheory.DedekindDomain.Factorization
public import Mathlib.RingTheory.FractionalIdeal.Basic
public import Mathlib.RingTheory.FractionalIdeal.Operations
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat
open Formalism.DivisionValues (vw lw)

namespace GlobalTheory.SumSize.Model

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}


theorem loss_mono {dl : PlL D → ℝ} {B B' : ℝ} (h : Loss dl B) (hB : B ≤ B') : Loss dl B' :=
  ⟨h.1, h.2.1, fun s => (h.2.2 s).trans hB⟩

theorem lossLe_mul {w : PlL D} {z z' : ℂ} {a a' : ℝ} (h : LossLe w z a) (h' : LossLe w z' a') : LossLe w (z * z') (a + a') := by
  obtain ⟨y, rfl, h⟩ := h
  obtain ⟨y', rfl, h'⟩ := h'
  refine ⟨y * y', map_mul _ _ _, ?_⟩
  by_cases hy : y = 0
  · exact Or.inl (by rw [hy, zero_mul])
  by_cases hy' : y' = 0
  · exact Or.inl (by rw [hy', mul_zero])
  refine Or.inr ?_
  have e : vw w (y * y') = vw w y + vw w y' := by
    rw [vw, vw, vw, ← FractionalIdeal.spanSingleton_mul_spanSingleton, FractionalIdeal.count_mul] <;>
      simpa [FractionalIdeal.spanSingleton_eq_zero_iff]
  have a1 := h.resolve_left hy
  have a2 := h'.resolve_left hy'
  rw [e]; push_cast; linarith

end GlobalTheory.SumSize.Model

end
