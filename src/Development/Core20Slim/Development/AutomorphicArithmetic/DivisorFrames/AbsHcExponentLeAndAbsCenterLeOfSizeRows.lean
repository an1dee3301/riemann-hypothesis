module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParameterSizeConditionsNumericBounds
public import Development.AbelianVarietyTheory.Definitions.Divisors.LeastSplitAuxiliaryPrimeThetaChainSpec
public import Batteries.Classes.RatCast
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LevelPlusSubgroup
public import Development.AbelianVarietyTheory.Definitions.Foundations.StrictInterlaceIffDescEnum
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataParams
public import Formalism.LocalRingCardinality.DataParamsT
public import Formalism.LocalRingCardinality.DataParams₂
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
public import Formalism.SharpRestriction.ElevenLe
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.NeZero
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Init.SizeOf
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
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
public import Mathlib.Algebra.Order.Group.Defs
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
public import Mathlib.Algebra.Order.Ring.Cast
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Ring.Rat
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Ring.Unbundled.Basic
public import Mathlib.Algebra.Order.Ring.Unbundled.Rat
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Algebra.Order.Star.Rat
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Order.Sub.Basic
public import Mathlib.Algebra.Order.ZeroLEOne
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Algebra.Star.Rat
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.Real.Star
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.NNRat.Defs
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Cast.Order.Basic
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Rat.Cast.CharZero
public import Mathlib.Data.Rat.Cast.Defs
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Data.Rat.Defs
public import Mathlib.Data.Rat.Floor
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.Logic.Function.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Lattice
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.Tactic.CancelDenoms.Core
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Positivity.Core
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw
  GlobalTheory.FunObj.borelSpaceKw

theorem UpperTheory.abs_hc_exponent_le_and_abs_center_le_of_sizeRows :
    ∀ (D : D7) (large₂ : SizeData₂ D), GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows large₂ → HostHyp D → (∀ τ l, |(((D.hc τ).e l : ℚ) : ℝ)| ≤ 4 * large₂.sc.b) ∧ ∀ τ i, 1 ≤ i → i ≤ D.R.m → |((cen D 1 τ i : ℤ) : ℝ)| ≤ 2 * large₂.sc.b := by
  intro D large₂ hS hH
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hb, he, -⟩ := hS
  have hbpos : 0 < large₂.sc.b := by
    have := large₂.Sc_pos
    have : (0 : ℝ) ≤ (↑D.R.m + 1) * ↑(gap D 1) := by positivity
    linarith
  refine ⟨fun τ l => ?_, fun τ i hi him => ?_⟩
  · obtain ⟨hb0, he0⟩ := he τ l
    have hg := ((hH.gap τ l).1)
    have ht : (0 : ℚ) ≤ ((D.R.t : ℚ) + 3) / 2 := by positivity
    have hepos : (0 : ℚ) ≤ (D.hc τ).e l := by linarith
    have hepos' : (0 : ℝ) ≤ (((D.hc τ).e l : ℚ) : ℝ) := by exact_mod_cast hepos
    rw [abs_of_nonneg hepos']
    exact he0
  · set G := GlobalTheory.SignedHC.GridData.ofHCParam (D.hc τ) (sLen D) (gap D 1) 0 with hG
    have hcen : cen D 1 τ i = ⌊G.mid i⌋ := rfl
    have hmid : G.mid i = G.a i + (G.ga : ℚ) / 2 := G.mid_eq hi
    have ha : G.a i = (G.v 2 : ℚ) + 1 / 2 + ((G.m : ℚ) + 1 - i) * G.ga := rfl
    have hm : G.m = D.R.m := rfl
    have hga : G.ga = gap D 1 := rfl
    have hv : 0 ≤ G.v 2 ∧ ((G.v 2 : ℚ) : ℝ) ≤ large₂.Sc := by
      by_cases hk : 0 < D.R.k - 1
      · have hv2 : G.v 2 = ⌊(D.hc τ).v ⟨0, hk⟩⌋ := by
          simp [hG, GlobalTheory.SignedHC.GridData.ofHCParam, GlobalTheory.SignedHC.GridData.extend, hk]
        obtain ⟨h0, h1⟩ := large₂.cloud_v τ ⟨0, hk⟩
        have h0' : (0 : ℚ) ≤ (D.hc τ).v ⟨0, hk⟩ := by exact_mod_cast h0
        refine ⟨?_, ?_⟩
        · rw [hv2]
          exact Int.floor_nonneg.mpr h0'
        · rw [hv2]
          have hfl : ((⌊(D.hc τ).v ⟨0, hk⟩⌋ : ℤ) : ℚ) ≤ (D.hc τ).v ⟨0, hk⟩ := Int.floor_le _
          have hfl' : ((((⌊(D.hc τ).v ⟨0, hk⟩⌋ : ℤ) : ℚ)) : ℝ) ≤ (((D.hc τ).v ⟨0, hk⟩ : ℚ) : ℝ) := by
            exact_mod_cast hfl
          linarith
      · have hv2 : G.v 2 = 0 := by
          simp [hG, GlobalTheory.SignedHC.GridData.ofHCParam, GlobalTheory.SignedHC.GridData.extend, hk]
        rw [hv2]
        refine ⟨le_rfl, ?_⟩
        simpa using large₂.Sc_pos.le
    obtain ⟨hv0, hv1⟩ := hv
    have hi' : (1 : ℚ) ≤ i := by exact_mod_cast hi
    have him' : (i : ℚ) ≤ D.R.m := by exact_mod_cast him
    have hga0 : (0 : ℚ) ≤ G.ga := by positivity
    have hv0' : (0 : ℚ) ≤ G.v 2 := by exact_mod_cast hv0
    have hmid0 : 0 ≤ G.mid i := by
      rw [hmid, ha, hm]
      have : (0 : ℚ) ≤ ((D.R.m : ℚ) + 1 - i) * G.ga := mul_nonneg (by linarith) hga0
      linarith
    have hmid1 : ((G.mid i : ℚ) : ℝ) ≤ large₂.sc.b := by
      have e1 : ((G.mid i : ℚ) : ℝ) = ((G.v 2 : ℚ) : ℝ) + 1 / 2 + (((D.R.m : ℝ) + 1 - i) * (gap D 1 : ℝ)) + (gap D 1 : ℝ) / 2 := by
        rw [hmid, ha, hm, hga]
        push_cast
        ring
      have hgr : (0 : ℝ) ≤ (gap D 1 : ℝ) := by positivity
      have hir : (1 : ℝ) ≤ i := by exact_mod_cast hi
      have : ((D.R.m : ℝ) + 1 - i) * (gap D 1 : ℝ) + (gap D 1 : ℝ) / 2 ≤ ((D.R.m : ℝ) + 1) * (gap D 1 : ℝ) := by
        nlinarith
      linarith
    have hf0 : 0 ≤ cen D 1 τ i := by
      rw [hcen]
      exact Int.floor_nonneg.mpr hmid0
    have hf1 : ((cen D 1 τ i : ℤ) : ℝ) ≤ large₂.sc.b := by
      rw [hcen]
      have hfl : ((⌊G.mid i⌋ : ℤ) : ℚ) ≤ G.mid i := Int.floor_le _
      have hfl' : ((((⌊G.mid i⌋ : ℤ) : ℚ)) : ℝ) ≤ ((G.mid i : ℚ) : ℝ) := by exact_mod_cast hfl
      have : (((⌊G.mid i⌋ : ℤ)) : ℝ) = ((((⌊G.mid i⌋ : ℤ) : ℚ)) : ℝ) := by push_cast; rfl
      linarith
    have hf0' : (0 : ℝ) ≤ ((cen D 1 τ i : ℤ) : ℝ) := by exact_mod_cast hf0
    rw [abs_of_nonneg hf0']
    linarith
