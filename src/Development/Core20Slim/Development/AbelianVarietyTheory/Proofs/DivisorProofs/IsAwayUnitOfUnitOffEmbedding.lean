module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegIdxOfIsStd
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseFits
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.GSEqZeroOfLt
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsMulPowIntegral
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSplitChartSplitChart
public import Development.Core20Slim.Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.CentralInvolutionRing
public import Development.AbelianVarietyTheory.Definitions.Foundations.TupleConstantsNeZero
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Function
public import Init.Data.Int.Basic
public import Init.Data.Nat.Div.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.GroupWithZero.Units.Lemmas
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Inv
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
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (gauss unifAt PsiUnr)

theorem GlobalTheory.Square.isAwayUnit_of_unitOff_embedding : ∀ {K : Type} [Field K] [NumberField K] (σ : K →+* ℂ) (x : K) (q m : ℕ), 0 < q → q ∣ m →
    GlobalTheory.IndefiniteRowSideFullHecke.CentralInvolutionRing.UnitOff q (σ x) → GlobalTheory.Square.IsAwayUnit m x := by
  intro K _ _ σ x q m hq hqm h
  obtain ⟨hx0, n, h1, h2⟩ := h
  have hx : x ≠ 0 := fun h0 => hx0 (by rw [h0, map_zero])
  have hinj : Function.Injective σ.toIntAlgHom := σ.injective
  have i1 : (q : K) ^ n * x ∈ integralClosure ℤ K := by
    rw [mem_integralClosure_iff, ← isIntegral_algHom_iff σ.toIntAlgHom hinj]
    simpa using h1
  have i2 : (q : K) ^ n * x⁻¹ ∈ integralClosure ℤ K := by
    rw [mem_integralClosure_iff, ← isIntegral_algHom_iff σ.toIntAlgHom hinj]
    simpa using h2
  set a : 𝓞 K := ⟨_, i1⟩ with ha_def
  set b : 𝓞 K := ⟨_, i2⟩ with hb_def
  have ha : algebraMap (𝓞 K) K a = (q : K) ^ n * x := rfl
  have hb : algebraMap (𝓞 K) K b = (q : K) ^ n * x⁻¹ := rfl
  obtain ⟨d, rfl⟩ := hqm
  refine GlobalTheory.Square.AwayClosure.of_integral (k := n) (l := n) (a := a * (d : 𝓞 K) ^ n)
    (b := b * (d : 𝓞 K) ^ n) hx ?_ ?_
  · rw [RingOfIntegers.coe_eq_algebraMap, map_mul, map_pow, map_natCast, ha]
    push_cast
    ring
  · rw [RingOfIntegers.coe_eq_algebraMap, map_mul, map_pow, map_natCast, hb]
    push_cast
    ring
