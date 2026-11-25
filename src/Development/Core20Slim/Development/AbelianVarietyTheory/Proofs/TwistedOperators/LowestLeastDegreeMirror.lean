module

public import Mathlib
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegWBlattnerLeOfBlattnerConeStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowestKTypesJointShapeBlockUnitaryStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowestKTypesJointShapeBlockInUnitarySStatement
public import Batteries.Classes.RatCast
public import Formalism.LocalRingCardinality.DataTheta
public import Init.Classical
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.List.Basic
public import Init.Data.List.Lemmas
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.GetElem
public import Init.Prelude
public import Init.PropLemmas
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Order.Group.Defs
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.Ring.Rat
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Ring.Unbundled.Rat
public import Mathlib.Algebra.Order.Star.Rat
public import Mathlib.Algebra.Order.ZeroLEOne
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Algebra.Star.Rat
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.List.GetD
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Cast.Order.Basic
public import Mathlib.Data.Rat.Defs
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Tactic.CancelDenoms.Core
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg

namespace GlobalTheory.LeastDegree

theorem lamA_ne_zero {t : ℕ} {al be ga de : List ℚ} (h : HypA t al be ga de)
    (a : Ix (al.length + be.length) (ga.length + de.length)) : lamA al be ga de a ≠ 0 := by
  obtain ⟨ht, -, -, -, -, -, -, -, -, -, habs⟩ := h
  have key : ∀ e ∈ al ++ be ++ ga ++ de, e ≠ 0 := by
    intro e he h0
    have hle := habs e he
    rw [h0, abs_zero] at hle
    have ht' : (1 : ℚ) ≤ t := by exact_mod_cast ht
    linarith
  rcases a with ⟨i, hi⟩ | ⟨j, hj⟩
  · have hi' : i < (al ++ be).length := by simpa using hi
    have hm : (al ++ be)[i] ∈ al ++ be := List.getElem_mem hi'
    simp only [lamA, ofBlocks, List.getD_eq_getElem _ _ hi']
    apply key
    simp only [List.mem_append] at hm ⊢
    tauto
  · have hj' : j < (ga ++ de).length := by simpa using hj
    have hm : (ga ++ de)[j] ∈ ga ++ de := List.getElem_mem hj'
    simp only [lamA, ofBlocks, List.getD_eq_getElem _ _ hj']
    apply key
    simp only [List.mem_append] at hm ⊢
    tauto

theorem coneTypes_ds (X : ProvA) (hX : DiscreteSeriesBlattner X) {p q : ℕ} {lam : Ix p q → ℚ}
    (h : IsParam lam) : ConeTypes (X.ds p q lam).HK lam := by
  intro μ v hv
  exact (hX p q lam h).2.2 μ v hv

theorem lowest_least_degree : ∀ X : ProvA, DiscreteSeriesBlattner X → ∀ (t : ℕ) (al be ga de : List ℚ), HypA t al be ga de → (∀ μ v, IsHW (X.ds _ _ (lamA al be ga de)).HK.act μ v → degW (cPair (al.length + de.length + t) (ga.length + be.length)) (blattner (lamA al be ga de)) ≤ degW (cPair (al.length + de.length + t) (ga.length + be.length)) μ) ∧ (∀ μ v, IsHW (X.ds _ _ (lamA' t al be ga de)).HK.act μ v → degW (cPair (al.length + be.length) (ga.length + de.length)) (blattner (lamA' t al be ga de)) ≤ degW (cPair (al.length + be.length) (ga.length + de.length)) μ) := by
  intro X hX t al be ga de hA
  obtain ⟨-, hP, hP', hs, hs'⟩ := GlobalTheory.T.lowest_kTypes_jointShape_block_unitary t al be ga de hA
  refine ⟨?_, ?_⟩
  · refine GlobalTheory.T.degW_blattner_le_of_blattnerCone _ _ _ _ _ 0 (coneTypes_ds X hX hP) ?_
    intro a
    refine ⟨(hs a).1, fun hle => (hs a).2 ?_⟩
    exact lt_of_le_of_ne hle (lamA_ne_zero hA a)
  · exact GlobalTheory.T.degW_blattner_le_of_blattnerCone _ _ _ _ _ ((t : ℚ) / 2) (coneTypes_ds X hX hP') hs'

theorem lowest_least_degree_mirror : ∀ X : ProvA, DiscreteSeriesBlattner X → ∀ (t : ℕ) (al be ga de : List ℚ), HypA t al be ga de → (∀ μ v, IsHW (X.ds _ _ (lamA al be ga de)).HK.act μ v → degW (cPair (al.length + de.length) (ga.length + be.length + t)) (blattner (lamA al be ga de)) ≤ degW (cPair (al.length + de.length) (ga.length + be.length + t)) μ) ∧ (∀ μ v, IsHW (X.ds _ _ (lamM' t al be ga de)).HK.act μ v → degW (cPair (al.length + be.length) (ga.length + de.length)) (blattner (lamM' t al be ga de)) ≤ degW (cPair (al.length + be.length) (ga.length + de.length)) μ) := by
  intro X hX t al be ga de hA
  obtain ⟨-, hP, -, -, -⟩ := GlobalTheory.T.lowest_kTypes_jointShape_block_unitary t al be ga de hA
  obtain ⟨-, hM, hs, hs'⟩ := GlobalTheory.T.lowestKTypes_jointShape_block_in_unitaryS t al be ga de hA
  refine ⟨?_, ?_⟩
  · refine GlobalTheory.T.degW_blattner_le_of_blattnerCone _ _ _ _ _ 0 (coneTypes_ds X hX hP) ?_
    intro a
    refine ⟨(hs a).1, fun hle => (hs a).2 ?_⟩
    exact lt_of_le_of_ne hle (lamA_ne_zero hA a)
  · exact GlobalTheory.T.degW_blattner_le_of_blattnerCone _ _ _ _ _ ((t : ℚ) / 2) (coneTypes_ds X hX hM) hs'

end GlobalTheory.LeastDegree
