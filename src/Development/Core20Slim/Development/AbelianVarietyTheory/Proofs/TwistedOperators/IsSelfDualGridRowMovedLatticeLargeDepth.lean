module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.TiltSc
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiDiagonalEpsilonGramMulVec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StaircaseIdealConjugateInverse
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemMulInvIff
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
public import Development.Core20Slim.Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataParams₂
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.Divisibility.LiftLat
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Fin.Basic
public import Init.Data.Fin.Lemmas
public import Init.Data.Int.Basic
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
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.IsField
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Even
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Ring.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Basic
public import Mathlib.RingTheory.FractionalIdeal.Basic
public import Mathlib.RingTheory.FractionalIdeal.Inverse
public import Mathlib.RingTheory.FractionalIdeal.Operations
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open scoped nonZeroDivisors

namespace GlobalTheory.RowShape

variable {D : D7}

theorem mem_spanSingleton_mul_iff {s x : D.host.E} (hs : s ≠ 0) (I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) :
    x ∈ FractionalIdeal.spanSingleton _ s * I ↔ x * s⁻¹ ∈ I := by
  rw [FractionalIdeal.mem_singleton_mul]
  constructor
  · rintro ⟨z, hz, rfl⟩
    rwa [mul_comm, ← mul_assoc, inv_mul_cancel₀ hs, one_mul]
  · intro h
    exact ⟨x * s⁻¹, h, by rw [mul_comm, mul_assoc, inv_mul_cancel₀ hs, mul_one]⟩

theorem tiltSc_ne_zero (j : ℕ) (p : Fin (D.R.m - 1 - j)) : tiltSc D j p ≠ 0 := by
  unfold tiltSc
  split_ifs
  · exact inv_ne_zero (pow_ne_zero _ cmHost_imaginaryGenerator_ne_zero)
  · exact star_ne_zero.2 (pow_ne_zero _ cmHost_imaginaryGenerator_ne_zero)
  · exact one_ne_zero

theorem tiltSc_mul_star_rev (j : ℕ) (p : Fin (D.R.m - 1 - j)) : tiltSc D j p * star (tiltSc D j p.rev) = 1 := by
  have hx : D.host.xi0 ≠ 0 := cmHost_imaginaryGenerator_ne_zero
  obtain ⟨a, ha⟩ := D.R.m_even
  have hp := p.2
  unfold tiltSc
  by_cases hj : Odd j
  · obtain ⟨b, hb⟩ := hj
    have hj' : Odd j := ⟨b, hb⟩
    rw [if_pos hj', if_pos hj', Fin.val_rev]
    by_cases h1 : 2 * p.1 < D.R.m - 1 - j
    · rw [if_pos h1, if_neg (by omega)]
      have e : D.R.m - 1 - j - 1 - (D.R.m - 1 - j - (p.1 + 1)) = p.1 := by omega
      rw [e, star_star, inv_mul_cancel₀ (pow_ne_zero _ hx)]
    · rw [if_neg h1, if_pos (by omega)]
      have e : D.R.m - 1 - j - (p.1 + 1) = D.R.m - 1 - j - 1 - p.1 := by omega
      rw [e, star_inv₀, mul_inv_cancel₀ (star_ne_zero.2 (pow_ne_zero _ hx))]
  · rw [if_neg hj, if_neg hj, star_one, one_mul]

theorem rowId_ne_zero_and_dual (j : ℕ) (p : Fin (D.R.m - 1 - j)) :
    rowId D j p ≠ 0 ∧ ∀ x, x ∈ rowId D j p.rev ↔ star x ∈ (rowId D j p)⁻¹ := by
  obtain ⟨hA, hconj⟩ := (GlobalTheory.ChiGrid.StairConj.conj_AA_and_stA D).1
  obtain ⟨h0, hd⟩ := GlobalTheory.ChiGrid.stairId_ne_zero_and_mem_rev_iff D _ _ hA hconj (D.R.m - 1 - j) p
  have hs := tiltSc_ne_zero (D := D) j p
  have hs' := tiltSc_ne_zero (D := D) j p.rev
  refine ⟨mul_ne_zero (FractionalIdeal.spanSingleton_ne_zero_iff.2 hs) h0, fun x => ?_⟩
  unfold rowId
  rw [mul_inv, FractionalIdeal.spanSingleton_inv, mem_spanSingleton_mul_iff hs', mem_spanSingleton_mul_iff (inv_ne_zero hs),
    inv_inv, hd, star_mul', star_inv₀]
  have e : (star (tiltSc D j p.rev))⁻¹ = tiltSc D j p := by
    exact inv_eq_of_mul_eq_one_left (tiltSc_mul_star_rev j p)
  rw [e]

variable {T : Type} {L : LevCh D T} {sc : Consts}

theorem isSelfDualC_rowN (G : GridData L sc) (j : ℕ) (hj : j ≤ D.R.m) : IsSelfDualC _ (rowN G j) := by
  unfold rowN
  split_ifs with h
  · refine GlobalTheory.ChiGrid.SumDual.isSelfDualC_lat D _ _ _ _ (G.rowDec j h) _ _ (Or.inr rfl)
      (G.isV (X := .top j) hj (fun _ h' => by cases h')).sd (fun p => (rowId_ne_zero_and_dual j p).1)
      (fun p x => (rowId_ne_zero_and_dual j p).2 x)
  · exact (G.isV (X := .grid D.R.m j) ⟨le_rfl, hj⟩ (fun _ h' => by
      have := D.R.two_le_m
      injection h' with h1; omega)).sd

end GlobalTheory.RowShape

theorem GlobalTheory.RowShape.big_isSelfDualC_rowN :
    Big fun {D} {Γ} _ _ {Pl0 T} {A} {Ks} _ _ _ {R} ch => ∀ j, j ≤ D.R.m → IsSelfDualC _ (GlobalTheory.RowShape.rowN ch.G j) :=
  ⟨0, fun _ _ _ => ⟨0, fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ch _ _ j hj => GlobalTheory.RowShape.isSelfDualC_rowN ch.G j hj⟩⟩

end
