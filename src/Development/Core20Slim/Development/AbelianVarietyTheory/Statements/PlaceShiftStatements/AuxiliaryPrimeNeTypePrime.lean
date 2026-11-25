module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyGridDataIff
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Development.AbelianVarietyTheory.Definitions.Divisors.LeastSplitAuxiliaryPrimeThetaChainSpec
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataParams₂
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Classical
public import Init.Core
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
public import Init.Omega.Logic
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Even
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Hom.Instances
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Order.Kleene
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Logic.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Empty
public import Mathlib.Data.Finset.Filter
public import Mathlib.Data.Finset.Lattice.Basic
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.MinMax
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import ReciprocityTheory.NeutralLocalFields.Reciprocity

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.IndefR Formalism.IndefR.Links IsDedekindDomain NumberField
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum

namespace GlobalTheory.SqTop.Model

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}


theorem gBig_and {Q Q' : GP} (h : GBig @Q) (h' : GBig @Q') :
    GBig fun G μ C x b => Q G μ C x b ∧ Q' G μ C x b := by
  obtain ⟨c, h⟩ := h
  obtain ⟨c', h'⟩ := h'
  refine ⟨max c c', fun ε CF hCF => ?_⟩
  obtain ⟨C0, x0, h⟩ := h ε CF (le_of_max_le_left hCF)
  obtain ⟨C1, x1, h'⟩ := h' ε CF (le_of_max_le_right hCF)
  exact ⟨max C0 C1, max x0 x1, fun C hC D large₂ a b r T Lc μ hL G =>
    ⟨h C (le_of_max_le_left hC) D large₂ a (le_of_max_le_left b) r T Lc μ hL G,
      h' C (le_of_max_le_right hC) D large₂ a (le_of_max_le_right b) r T Lc μ hL G⟩⟩

theorem tower_numbers (i j : Fin D.R.m) : e0 D i j + pp D j = eTop D i j + qq D j ∧
    halfRank D i j = h0 D i j + pp D j + qq D j ∧ pp D j + qq D j = D.R.m - 1 - j ∧ 1 ≤ e0 D i j ∧ e0 D i j < h0 D i j ∧
    botBig D i j = e0 D i j + h0 D i j ∧ botSmall D i j + e0 D i j = h0 D i j ∧ eTop D i j + qq D j ≤ halfRank D i j ∧
    halfRank D i j ≤ bigN D := by
  obtain ⟨h1, h2, h3⟩ := ranks_exact D i j
  obtain ⟨u, hu⟩ := D.R.t_odd
  obtain ⟨v, hv⟩ := odd_sLen D
  obtain ⟨a, ha⟩ := D.R.m_even
  have e : rankV D (i + 1) (j + 1) = rankV D i j + D.R.t + sLen D := by simp only [rankV]; ring
  have r1 : D.R.r ≤ rankV D i j := by simp only [rankV]; omega
  have r2 := D.R.m_add_three_le_k
  have r3 : D.R.r = D.R.k + D.R.m - 1 := rfl
  have r4 : sLen D = D.R.r + 6 := rfl
  have hj := j.2
  have b1 : (j.1 + 1) * D.R.t ≤ D.R.m * D.R.t := Nat.mul_le_mul_right _ j.2
  have b2 : (i.1 + 1) * sLen D ≤ D.R.m * sLen D := Nat.mul_le_mul_right _ i.2
  have b3 : rankV D (i + 1) (j + 1) = D.R.r + (j.1 + 1) * D.R.t + (i.1 + 1) * sLen D := rfl
  have b4 : bigN D = D.R.k + (D.R.m * D.R.t + D.R.m * sLen D + D.R.m) := by simp only [bigN]; ring
  simp only [e0, h0, pp, qq, eTop]
  omega

variable {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData Lc sc) {μ₀ : T}

theorem base_tuple (hL : Lc.Is μ₀) : twPl G μ₀ = ∅ ∧ Qn G μ₀ = 1 ∧ modT G μ₀ = SqNum.condE G.pl := by
  have h : twPl G μ₀ = ∅ := by
    refine Finset.eq_empty_of_forall_notMem fun w hw => ?_
    simp only [twPl, locPl, Finset.mem_filter, Finset.mem_union] at hw
    exact (hL.Q_ram μ₀ w).2 (Or.inl (hw.1.resolve_left hw.2)) (by rw [hL.xi_base]; intro x _; rfl)
  simp [Qn, modT, h]

theorem Qn_ne_zero (t : T) : Qn G t ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun w _ => Ideal.absNorm_eq_zero_iff.not.2 w.ne_bot

end GlobalTheory.SqTop.Model

end
