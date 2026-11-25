module

public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialDescentEstimate
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LeafInfinitePlaceBound
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Realised
public import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
public import Development.AbelianVarietyTheory.Definitions.Divisors.TwistedPlaceChoiceLiesOverPair
public import Formalism.LocalRingCardinality.DataDIV
public import Formalism.LocalRingCardinality.DataErr
public import Formalism.LocalRingCardinality.DataExtra
public import Formalism.LocalRingCardinality.DataGatTies
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataParams₂
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.Divisibility.HeckeRI
public import Formalism.LocalToGlobal.Divisibility.InertRationalAdjoint
public import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.FunctionalLowerBoundOfConditionsNumeric
public import Formalism.SharpRestriction.FamCore
public import Formalism.SharpRestriction.GlobalTheoremInputs
public import Formalism.SharpRestriction.GrowthBounds.IsResidueClassZero
public import Formalism.SharpRestriction.ParConsts
public import Formalism.SharpRestriction.ParamsHeightRankConstant
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Fin.Basic
public import Init.Data.Int.Basic
public import Init.Data.List.Basic
public import Init.Data.List.BasicAux
public import Init.Data.List.Lemmas
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Cast.Order.Ring
public import Mathlib.Data.Nat.Init
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Lattice
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Positivity.Core
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions NumberField Formalism.L2.Indef Formalism.L2.Indef.Tree GlobalTheory.BigTop GlobalTheory.BigTop.Fun
namespace GlobalTheory.BigTop.Fun.PolBound
end GlobalTheory.BigTop.Fun.PolBound
namespace GlobalTheory.BigTop.Fun.PolBound
open Formalism.BasicNotions Formalism.MainNotions NumberField
end GlobalTheory.BigTop.Fun.PolBound
namespace GlobalTheory.BigTop.Fun
open Formalism.BasicNotions Formalism.MainNotions NumberField GlobalTheory.BigTop.Fun.PolBound
theorem desPol_alt : DescentPolynomialCondition := by
  refine ⟨0, fun CF _ => ?_⟩
  refine ⟨1 / 52, by norm_num, fun eps _ _ =>
    ⟨⟨0, fun _ => 0, fun l => 16 * ((⌈|l.getD 0 0|⌉₊ : ℝ) + 1 + 9) + 1, fun _ => 0⟩, fun Fm CH _ hL => ?_⟩⟩
  intro _
  have hCH : 16 * ((⌈|Fm.Ct|⌉₊ : ℝ) + 1 + 9) + 1 ≤ CH := hL.2.2.1 CH (by simp [FamP.cMid])
  refine ⟨1, fun C hC => ?_⟩
  refine ⟨max (13000000000 * C ^ 4) 1, fun x hx hxle i p _ d _ => ?_⟩
  set T : ℕ := ⌈|Fm.Ct|⌉₊ + 1 with hTdef
  have hT : (Fm.L x i).Ct + 1 ≤ T := by
    rw [Fm.Ct_eq, hTdef]; push_cast; linarith [le_abs_self Fm.Ct, Nat.le_ceil |Fm.Ct|]
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := factors_le (Fm.L x i) (Fm.sizes x hx i) T hT
  set X := (Fm.L x i).sc.x with hXdef
  have hX1 : 1 ≤ X := (Fm.L x i).sc.one_lt_alt.le
  have hXA : 13000000000 * C ^ 4 ≤ X := by
    rw [hXdef, Fm.L_x x i hx]; exact (le_max_left _ _).trans hxle
  set D := Fm.D x i
  have eN : ((D.R.k + D.R.m * (D.R.t + (D.R.k + D.R.m + 5) + 1) : ℕ) : ℝ) =
      (D.R.k : ℝ) + D.R.m * (D.R.t + (D.R.k + D.R.m + 5) + 1) := by push_cast; ring
  have enr : ((D.R.k + D.R.m : ℕ) : ℝ) = (D.R.k : ℝ) + D.R.m := by push_cast; ring
  have e : d.O.pol C p.Z.b = 100000 * C ^ 3 * (D.R.f : ℝ) * (D.R.m : ℝ) ^ 2 *
      ((D.R.k + D.R.m * (D.R.t + (D.R.k + D.R.m + 5) + 1) : ℕ) : ℝ) ^ 2 *
      (((D.R.k : ℝ) + D.R.m - 1) * ((D.R.k + D.R.m * (D.R.t + (D.R.k + D.R.m + 5) + 1) : ℕ) : ℝ) *
        Real.log (Fm.L x i).sc.b + C * (D.R.f : ℝ) ^ 2 * ((D.R.k + D.R.m : ℕ) : ℝ) ^ 6 *
        Real.log ((Fm.L x i).sc.b * ((D.R.k + D.R.m : ℕ) : ℝ) * (D.host.g 0 : ℝ) * (D.host.g 1 : ℝ) *
          (D.host.pde : ℝ) * (D.host.pde' : ℝ) * |((discr D.host.E : ℤ) : ℝ)|)) := rfl
  show d.O.pol C p.Z.b ≤ X ^ CH
  rw [e, eN, enr]
  rw [enr] at h7
  have key := pol_core hC (one_le_pow₀ hX1) (Nat.cast_nonneg _) h1 (Nat.cast_nonneg _) h2 (Nat.cast_nonneg _) h3
    (Nat.cast_nonneg _) h4 h6 h5 h7
  refine key.trans ?_
  have hp : (X ^ (T + 9)) ^ 16 = X ^ (16 * (T + 9)) := by rw [← pow_mul, mul_comm]
  have hC4 : 0 ≤ 13000000000 * C ^ 4 := by positivity
  calc 13000000000 * C ^ 4 * (X ^ (T + 9)) ^ 16 ≤ X * X ^ (16 * (T + 9)) := by
        rw [hp]; exact mul_le_mul_of_nonneg_right hXA (by positivity)
    _ = X ^ ((16 * (T + 9) + 1 : ℕ) : ℝ) := by rw [Real.rpow_natCast, pow_succ, mul_comm]
    _ ≤ X ^ CH := by
        refine rpow_mono hX1 ?_
        rw [hTdef] at *
        push_cast
        linarith
end GlobalTheory.BigTop.Fun
end
