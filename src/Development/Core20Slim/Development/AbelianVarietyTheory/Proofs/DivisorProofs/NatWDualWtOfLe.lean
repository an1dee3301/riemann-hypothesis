module

public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopDlNonneg
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DerivationDenominatorsAndHostFieldSizes
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteKernelNodeRankLeTotalRank
public import Batteries.Classes.RatCast
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LevelPlusSubgroup
public import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
public import Development.AbelianVarietyTheory.Definitions.Divisors.LeastSplitAuxiliaryPrimeThetaChainSpec
public import Development.AbelianVarietyTheory.Definitions.Foundations.StrictInterlaceIffDescEnum
public import Formalism.LocalRingCardinality.DataCoeff
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataParams
public import Formalism.LocalRingCardinality.DataParamsT
public import Formalism.LocalRingCardinality.DataParams₂
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.ElevenLe
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Classical
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Fin.Basic
public import Init.Data.Fin.Lemmas
public import Init.Data.Int.Basic
public import Init.Data.Int.Lemmas
public import Init.Data.Int.Order
public import Init.Data.Nat.Basic
public import Init.Data.Nat.Div.Basic
public import Init.Data.NeZero
public import Init.Data.Order.Lemmas
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Algebra.Order.Group.Abs
public import Mathlib.Algebra.Order.Group.Defs
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
public import Mathlib.Algebra.Order.Ring.Cast
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Ring.Rat
public import Mathlib.Algebra.Order.Ring.Unbundled.Basic
public import Mathlib.Algebra.Order.Ring.Unbundled.Rat
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.Real.Star
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Int.Cast.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Cast.Order.Basic
public import Mathlib.Data.Nat.Cast.Order.Ring
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Rat.Cast.CharZero
public import Mathlib.Data.Rat.Cast.Defs
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Data.Rat.Floor
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.Logic.Function.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Lattice
public import Mathlib.Order.Notation
public import Mathlib.Order.RelClasses
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.Tactic.CancelDenoms.Core
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.Linarith.Preprocessing
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.SignedHC

namespace GlobalTheory.GridWtBound

theorem natW_dual_wtOf_le (n : ℕ) (E : Finset ℚ) (M : ℝ) (hM : 0 ≤ M) (hE : ∀ x ∈ E, |(x : ℝ)| ≤ M) (a : Fin n) :
    (((wtOf n E).dual.natW a : ℕ) : ℝ) ≤ 2 * M + 1 := by
  have hn : 0 < n := a.pos
  have hrev : Fin.rev (⟨n - 1, by omega⟩ : Fin n) = ⟨0, hn⟩ := by ext; simp; omega
  have key : (wtOf n E).dual.natW a = ((wtOf n E).w ⟨0, hn⟩ - (wtOf n E).w a.rev).toNat := by
    simp only [DomWeight.natW, DomWeight.detShift, DomWeight.dual, dif_pos hn, hrev]
    congr 1; ring
  have hd : (((wtOf n E).w ⟨0, hn⟩ - (wtOf n E).w a.rev : ℤ) : ℝ) ≤ 2 * M + 1 := by
    unfold wtOf
    split_ifs with h
    · have e0 := hE _ (descEnum_mem E h.1 ⟨0, hn⟩)
      have e1 := hE _ (descEnum_mem E h.1 a.rev)
      have f0 : ((⌊highestWeight E h.1 ⟨0, hn⟩⌋ : ℤ) : ℝ) ≤ ((highestWeight E h.1 ⟨0, hn⟩ : ℚ) : ℝ) := by
        exact_mod_cast Int.floor_le _
      have f1 : ((highestWeight E h.1 a.rev : ℚ) : ℝ) - 1 < ((⌊highestWeight E h.1 a.rev⌋ : ℤ) : ℝ) := by
        exact_mod_cast Int.sub_one_lt_floor _
      have hr : (0 : ℝ) ≤ ((a.rev : ℕ) : ℝ) := Nat.cast_nonneg _
      have g0 : ((highestWeight E h.1 ⟨0, hn⟩ : ℚ) : ℝ) ≤ M - ((n : ℝ) - 1) / 2 := by
        simp only [highestWeight]; push_cast; linarith [(abs_le.1 e0).2]
      have g1 : -M - ((n : ℝ) - 1) / 2 ≤ ((highestWeight E h.1 a.rev : ℚ) : ℝ) := by
        simp only [highestWeight]; push_cast; linarith [(abs_le.1 e1).1]
      push_cast
      linarith
    · simp; linarith
  rw [key]
  have c : (((wtOf n E).w ⟨0, hn⟩ - (wtOf n E).w a.rev).toNat : ℝ) =
      (((((wtOf n E).w ⟨0, hn⟩ - (wtOf n E).w a.rev).toNat : ℤ)) : ℝ) := (Int.cast_natCast _).symm
  rw [c, Int.toNat_eq_max]
  push_cast
  exact max_le (by push_cast at hd; exact hd) (by linarith)

end GlobalTheory.GridWtBound

namespace GlobalTheory.GridWtBound

theorem extend_bounds {n : ℕ} (d : ℕ) (f : Fin n → ℚ) (h : ℝ) (hh : 0 ≤ h)
    (hf : ∀ i, 0 ≤ ((f i : ℚ) : ℝ) ∧ ((f i : ℚ) : ℝ) ≤ h) (j : ℕ) :
    0 ≤ ((GridData.extend d f j : ℤ) : ℝ) ∧ ((GridData.extend d f j : ℤ) : ℝ) ≤ h := by
  unfold GridData.extend
  split_ifs with hj
  · obtain ⟨h1, h2⟩ := hf ⟨j - d, hj⟩
    have a1 : (0 : ℚ) ≤ f ⟨j - d, hj⟩ := by exact_mod_cast h1
    refine ⟨by exact_mod_cast Int.floor_nonneg.2 a1, le_trans ?_ h2⟩
    exact_mod_cast Int.floor_le _
  · simp [hh]

variable {D : D7}

end GlobalTheory.GridWtBound

namespace GlobalTheory.GridWtBound

theorem one_le_b {D : D7} (large₂ : SizeData₂ D) (hs : GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows large₂) : (1 : ℝ) ≤ large₂.sc.b := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hgap, -, -⟩ := hs
  have hSc := large₂.Sc_pos
  have hsg : sLen D < gap D 1 := sLen_lt_gap D 1
  have hg1 : (1 : ℝ) ≤ (gap D 1 : ℝ) := by exact_mod_cast (by omega : 1 ≤ gap D 1)
  have hm0 : (0 : ℝ) ≤ (D.R.m : ℝ) := Nat.cast_nonneg _
  nlinarith

end GlobalTheory.GridWtBound
