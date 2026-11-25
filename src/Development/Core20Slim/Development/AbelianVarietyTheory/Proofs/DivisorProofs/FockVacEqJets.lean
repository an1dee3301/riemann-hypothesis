module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPeriodPairIdealCurveLattice
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTwoTorsionCMPointAllConjugates
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormSqMulGaussianLatticeTranslateEqShifted
public import Formalism.SharpRestriction.GlobalSchurBounds.Joints
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.LeastSplitAuxiliaryPrimeThetaChainSpec
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Int.Lemmas
public import Init.Data.Int.Order
public import Init.Data.Nat.Basic
public import Init.Data.Nat.Lemmas
public import Init.Data.Zero
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Even
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Nat.Even
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.GroupWithZero.Units.Lemmas
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Positivity.Core
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker

namespace GlobalTheory.FunObj

attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem period_ne_zero {D : D7} {δ : ℂ} (hδ : δ ≠ 0) (τ : D.what₂.Tau) : period δ τ ≠ 0 := by
  refine div_ne_zero hδ (Complex.ofReal_ne_zero.2 (Real.sqrt_ne_zero'.2 ?_))
  have : 0 < ‖tauE D τ D.host.xi0‖ := norm_pos_iff.2 ((_root_.map_ne_zero _).2 cmHost_imaginaryGenerator_ne_zero)
  positivity

theorem rank_grid_zero {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : ChiGrid.GridData L sc) (k : ℕ) (hk : k ≤ D.R.m) :
    (G.V (.grid 0 k)).rank = D.R.r + k * D.R.t := by
  have key : (columnBlock L k).sp.rank = D.R.r + k * D.R.t := by
    rcases hk.eq_or_lt with rfl | hk
    · rw [colY_m]; exact D.sp.X'_rank
    · rw [colY_lt L hk]
      exact (D.sp.Y_rank _ (min_le_right _ _)).trans (by rw [min_eq_left hk.le]; rfl)
  exact key

theorem rank_node {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : ChiGrid.GridData L sc) {X : Node}
    (h : X.InRange D.R.m) (h0 : ∀ j, X ≠ .grid 0 j) : (G.V X).rank = X.rank D := (G.isV h h0).rank

theorem even_rank_mul : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : ChiGrid.GridData L sc) (p : Pair T),
    DefPair D.R.m p → Even ((G.pS p).rank * (G.pT p).rank) := by
  intro D T L sc G p hp
  cases p with
  | chi i j =>
    obtain ⟨hi, rfl⟩ := hp
    have h1 : (G.pS (.chi i D.R.m)).rank = rankV D (i + 1) D.R.m :=
      rank_node G (X := .grid (i + 1) D.R.m) ⟨hi, le_rfl⟩ (fun j h => by cases h)
    have h2 : (G.pT (.chi i D.R.m)).rank = rankV D i D.R.m := by
      rcases i with _ | i
      · show (G.V (.grid 0 D.R.m)).rank = _
        rw [rank_grid_zero G _ le_rfl]; simp [rankV]
      · exact rank_node G (X := .grid (i + 1) D.R.m) ⟨by omega, le_rfl⟩ (fun j h => by cases h)
    rw [h1, h2]
    have hs : Odd (sLen D) := odd_sLen D
    have e : rankV D (i + 1) D.R.m = rankV D i D.R.m + sLen D := by simp only [rankV]; ring
    by_cases he : Even (rankV D i D.R.m)
    · exact he.mul_left _
    · refine Even.mul_right ?_ _
      rw [e, Nat.even_add]
      exact ⟨fun h => absurd h he, fun h => absurd h (Nat.not_even_iff_odd.2 hs)⟩
  | mu t i j => exact absurd hp id
  | core i => exact absurd hp id
  | top t j =>
    have h1 : (G.pS (.top t j)).rank = rankX D j :=
      rank_node G (X := .top j) (show j ≤ D.R.m by simp only [DefPair] at hp; omega) (fun j h => by cases h)
    rw [h1]
    exact (even_rankX D j).mul_right _


variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : ChiGrid.GridData L sc} (W : G.Weil)



theorem Normal.period_ne_zero {U : Set T} {N : Std G U} (Z : Normal W N) (τ : D.what₂.Tau) : period Z.δ τ ≠ 0 := by
  refine GlobalTheory.FunObj.period_ne_zero ?_ τ
  rintro h
  obtain ⟨L, hL⟩ := GlobalTheory.CurveLattice.exists_periodPair_one D D.host.ccK_ne_bot
  have e : Z.δ ^ 12 = Formalism.MainNotions.TaylorLogMetric.discr (Formalism.MainNotions.TaylorLogMetric.lamOf D D.host.ccK 1) := Z.crv.2
  rw [h] at e
  exact GlobalTheory.CurveLattice.discr_ne_zero _ L hL (by rw [← e]; simp)

end GlobalTheory.FunObj
