module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
public import Development.Core20Slim.Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOKEx
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasCompactSupportFlatIntegrand
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneCosetOfIsTensor
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationLeOneOfMem
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCoefficientBound
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatIntegrandFlippedTensorLocallyConstantCompact
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralUnfoldingVariablesMemFieldRange
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemVarLat
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteInfiniteScalarBounds
public import Formalism.LocalToGlobal.ExponentGrids.ExponentGridsProofs.NormaliserValuationBound
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ValBasic
public import Formalism.QuotientMetricDivisors.Statement
public import Init.Classical
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.GroupWithZero.Units.Lemmas
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Ring.Cast
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Empty
public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Int.Cast.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.NNRat.Defs
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Rat.Init
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Lattice
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Tactic.Ring.RingNF

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RowTest GlobalTheory.SumSize GlobalTheory.RowClaim
open Formalism.DivisionValues (vw lw)
open MeasureTheory ValuativeRel GlobalTheory.UnfoldLoss

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw
  GlobalTheory.FunObj.borelSpaceKw

namespace GlobalTheory.LossSum

theorem lossLe_sum_and_pow : ∀ {D : D7} (w : PlL D),
    (∀ {ι : Type} (s : Finset ι) (z : ι → ℂ) (a : ℝ), (∀ i ∈ s, LossLe w (z i) a) → LossLe w (∑ i ∈ s, z i) a) ∧
    ∀ q M : ℕ, 0 < q → LossLe w ((((q : ℝ)⁻¹ ^ M : ℝ)) : ℂ) ((M : ℝ) * (vw w ((q : ℕ) : D.what₂.LL) : ℝ)) := by
  intro D w
  refine ⟨?_, ?_⟩
  · intro ι s z a h
    classical
    induction s using Finset.induction_on with
    | empty => exact ⟨0, by simp, Or.inl rfl⟩
    | insert j s hj ih =>
      rw [Finset.sum_insert hj]
      obtain ⟨y1, e1, h1⟩ := h j (Finset.mem_insert_self _ _)
      obtain ⟨y2, e2, h2⟩ := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
      refine ⟨y1 + y2, by rw [map_add (f := _), e1, e2], ?_⟩
      by_cases hy1 : y1 = 0
      · subst hy1; simpa using h2
      by_cases hy2 : y2 = 0
      · subst hy2; simpa using h1
      have h1' := h1.resolve_left hy1
      have h2' := h2.resolve_left hy2
      by_cases h3 : y1 + y2 = 0
      · exact Or.inl h3
      right
      have h4 := Formalism.AtG.ValuationJets.vw_add w y1 y2 hy1 hy2 h3
      have h5 : ((min (vw w y1) (vw w y2) : ℤ) : ℝ) ≤ (vw w (y1 + y2) : ℝ) := by exact_mod_cast h4
      push_cast at h5
      exact le_trans (le_min h1' h2') h5
  · intro q M hq
    refine ⟨((q : D.what₂.LL)⁻¹) ^ M, by push_cast; simp, Or.inr ?_⟩
    have hq0 : ((q : D.what₂.LL)⁻¹) ≠ 0 := inv_ne_zero (by exact_mod_cast hq.ne')
    rw [GlobalTheory.ScalAA.vw_pow' w hq0, GlobalTheory.ScalAA.vw_inv']
    push_cast; ring_nf; rfl

end GlobalTheory.LossSum
