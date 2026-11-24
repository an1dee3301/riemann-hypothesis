module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegIdxOfIsStd
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitCharTriangle
public import Development.AbelianVarietyTheory.Definitions.Divisors.LeastSplitAuxiliaryPrimeThetaChainSpec
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HermitianOrthogonalExtensionData
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealPlaceLinesRelatedAndVanishOffPlace
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.RealPlaceAnalysis.Complexify
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Classical
public import Init.Core
public import Init.Data.Bool
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Int.DivMod.Basic
public import Init.Data.Int.DivMod.Bootstrap
public import Init.Data.Int.Lemmas
public import Init.Data.Int.Order
public import Init.Data.List.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Even
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Even
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.StageDict

open GlobalTheory.ChainFr Matrix

variable {D : D7}

theorem jm_eq_diag {k p : ℕ} {ε : Fin k → ℝ} (h : ∀ a : Fin k, (ε a = 1 ∧ a.val < p) ∨ (ε a = -1 ∧ p ≤ a.val)) :
    Formalism.REAL.Jm (fun a : Fin k => decide (a.val < p)) = Matrix.diagonal (fun a => (ε a : ℂ)) := by
  unfold Formalism.REAL.Jm
  congr 1
  funext a
  rcases h a with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · simp [h1, h2]
  · have : ¬ a.val < p := by omega
    simp [h1, this]

theorem isUnit_of_isONBasis {k p : ℕ} {G s B : Matrix (Fin k) (Fin k) ℂ} (h : IsONBasis G s B p) : IsUnit B := by
  obtain ⟨ε, hε, h1, -⟩ := h
  have hd : IsUnit (Matrix.diagonal fun a => (ε a : ℂ)).det := by
    rw [Matrix.det_diagonal]
    refine IsUnit.mk0 _ (Finset.prod_ne_zero_iff.2 fun a _ => ?_)
    rcases hε a with ⟨e, -⟩ | ⟨e, -⟩ <;> simp [e]
  rw [← h1, Matrix.det_mul, Matrix.det_mul] at hd
  rw [Matrix.isUnit_iff_isUnit_det]
  exact isUnit_of_mul_isUnit_right hd

def sigIdx {V : HSp D} (r : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Rig V) (h : r.Is) (τ : D.what₂.Tau) : ℕ := Classical.choose (h.2.2 τ).2

theorem sigIdx_spec {V : HSp D} (r : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Rig V) (h : r.Is) (τ : D.what₂.Tau) :
    IsONBasis (gramAt D V τ) (r.s τ) (r.B τ) (sigIdx r h τ) := Classical.choose_spec (h.2.2 τ).2

def rigFr {V : HSp D} (r : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Rig V) (h : r.Is) : Fr V where
  ε τ a := decide (a.val < sigIdx r h τ)
  fr τ := (r.B τ)⁻¹
  fr_unit τ := by
    have hu := isUnit_of_isONBasis (sigIdx_spec r h τ)
    exact (Matrix.isUnit_nonsing_inv_iff).2 hu
  fr_gram τ := by
    have hu := isUnit_of_isONBasis (sigIdx_spec r h τ)
    obtain ⟨ε, hε, h1, -⟩ := sigIdx_spec r h τ
    rw [jm_eq_diag hε, ← h1, Matrix.conjTranspose_nonsing_inv]
    have hu' : IsUnit (r.B τ)ᴴ.det := by
      rw [Matrix.det_conjTranspose]; exact ((Matrix.isUnit_iff_isUnit_det _).1 hu).star
    have hu0 : IsUnit (r.B τ).det := (Matrix.isUnit_iff_isUnit_det _).1 hu
    rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu0, Matrix.mul_one, ← Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ hu', Matrix.one_mul]

theorem onb_rigFr {V : HSp D} (r : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Rig V) (h : r.Is) (τ : D.what₂.Tau) : (rigFr r h).onb τ = r.B τ := by
  have hu0 : IsUnit (r.B τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (isUnit_of_isONBasis (sigIdx_spec r h τ))
  simp only [Fr.onb, rigFr]
  exact Matrix.nonsing_inv_nonsing_inv _ hu0

theorem cart_rigFr {V : HSp D} (r : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Rig V) (h : r.Is) (τ : D.what₂.Tau) : (rigFr r h).cart τ = r.s τ := by
  have hu0 : IsUnit (r.B τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (isUnit_of_isONBasis (sigIdx_spec r h τ))
  obtain ⟨ε, hε, -, h2⟩ := sigIdx_spec r h τ
  simp only [Fr.cart, rigFr]
  rw [Matrix.nonsing_inv_nonsing_inv _ hu0, jm_eq_diag hε, ← h2, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu0, Matrix.mul_one]

theorem cart_frSgn_true_rigFr {V : HSp D} (r : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Rig V) (h : r.Is) (τ : D.what₂.Tau) :
    (GlobalTheory.SquareComm.frSgn true (rigFr r h)).cart τ = -r.s τ := by
  rw [← cart_rigFr r h τ]
  simp only [Fr.cart, GlobalTheory.SquareComm.frSgn]
  have e' : Formalism.REAL.Jm (fun a => xor true ((rigFr r h).ε τ a)) = -Formalism.REAL.Jm ((rigFr r h).ε τ) := by
    ext a b
    by_cases hab : a = b
    · subst hab; cases h' : (rigFr r h).ε τ a <;> simp [Formalism.REAL.Jm, h']
    · simp [Formalism.REAL.Jm, hab]
  rw [e', Matrix.mul_neg, Matrix.neg_mul]

theorem cart_frSgn_false_rigFr {V : HSp D} (r : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Rig V) (h : r.Is) (τ : D.what₂.Tau) :
    (GlobalTheory.SquareComm.frSgn false (rigFr r h)).cart τ = r.s τ := by
  rw [← cart_rigFr r h τ]
  simp [Fr.cart, GlobalTheory.SquareComm.frSgn]

theorem stage_sizes (i j : Fin D.R.m) {p q a a' : ℕ} (hp : p ≤ pp D j) (hq : q ≤ qq D j)
    (ha : a + 2 * pp D j = rankV D (i + 1) (j + 1) + 2 * p) (ha' : a' + 2 * qq D j = rankV D i j + 2 * q) :
    Even (a + a') ∧ a' + 2 * (2 * (p + q) + 1) < a ∧ 2 * (p + q) + 1 < a' ∧
      a + a' ≤ rankV D (i + 1) (j + 1) + rankV D i j := by
  obtain ⟨u, hu⟩ := D.R.t_odd
  obtain ⟨v, hv⟩ := D.R.m_even
  obtain ⟨w, hw⟩ := D.R.k_even
  have e : rankV D (i + 1) (j + 1) = rankV D i j + D.R.t + sLen D := by simp only [rankV]; ring
  have r1 : rankV D i j = D.R.r + j.1 * D.R.t + i.1 * sLen D := rfl
  have r3 : D.R.r = D.R.k + D.R.m - 1 := rfl
  have r4 : sLen D = D.R.r + 6 := rfl
  have h1 := D.R.m_add_three_le_k
  have h2 := D.R.three_m_lt_t
  have h3 := D.R.two_le_m
  have hj := j.2
  simp only [pp, qq] at hp hq ha ha'
  refine ⟨Nat.even_iff.2 (by omega), by omega, by omega, by omega⟩

end GlobalTheory.StageDict

end
