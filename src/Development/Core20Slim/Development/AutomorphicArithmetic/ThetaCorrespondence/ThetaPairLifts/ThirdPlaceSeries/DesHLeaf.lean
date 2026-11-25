module

public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZetaDenominatorsFitFunction
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LeafInfinitePlaceBound
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Realised
public import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
public import Development.AbelianVarietyTheory.Definitions.Divisors.TwistedPlaceChoiceLiesOverPair
public import Formalism.LocalRingCardinality.DataDIV
public import Formalism.LocalRingCardinality.DataExtra
public import Formalism.LocalRingCardinality.DataGatTies
public import Formalism.LocalRingCardinality.DataKernels
public import Formalism.LocalRingCardinality.DataMink
public import Formalism.LocalRingCardinality.DataParams₂
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.Divisibility.HeckeRI
public import Formalism.LocalToGlobal.Divisibility.InertRationalAdjoint
public import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.FunctionalLowerBoundOfConditionsNumeric
public import Formalism.SharpRestriction.Divisibility.SmallFirstModulusBelowScale
public import Formalism.SharpRestriction.FamCore
public import Formalism.SharpRestriction.GlobalSchurBounds.Chosen
public import Formalism.SharpRestriction.GlobalSchurBounds.MainIn
public import Formalism.SharpRestriction.GlobalSchurBounds.WeightVectorSmallSharesEight
public import Formalism.SharpRestriction.GlobalTheoremInputs
public import Formalism.SharpRestriction.GrowthBounds.IsResidueClassZero
public import Formalism.SharpRestriction.LevelLetterCocycles.AlignN
public import Formalism.SharpRestriction.LevelLetterCocycles.TwGood
public import Formalism.SharpRestriction.PageFix
public import Formalism.SharpRestriction.ParConsts
public import Formalism.SharpRestriction.ParamsHeightRankConstant
public import Formalism.SharpRestriction.SmoothDesignExistence.DGamSmooth
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Nat.Div.Basic
public import Init.Data.NeZero
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.Group.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Ring.Unbundled.Basic
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Order.ZeroLEOne
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.Real.Star
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Cast.Order.Basic
public import Mathlib.Data.Nat.Init
public import Mathlib.Logic.Function.Defs
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Tactic.CancelDenoms.Core
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.Linarith.Preprocessing
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
noncomputable section
namespace GlobalTheory.BigTop.Fun.Close
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem desHLeaf_alt : DescentHeightCondition := by
  refine ⟨0, fun CF _ => ⟨1, one_pos, fun eps heps _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm CH hF _ => ?_⟩⟩⟩
  intro _
  refine ⟨0, fun C _ => ?_⟩
  have hW : PageWin Fm := hF.2.1
  refine ⟨max (Fm.x1 + 1) ((8 : ℝ) ^ (1 / eps)), fun x hx hx0 i p _ d _ => ?_⟩
  have hx1 : 1 < x := lt_trans Fm.one_lt_family_threshold hx
  have hx0' : (0 : ℝ) < x := by linarith
  have h8 : (8 : ℝ) ≤ x ^ (8 * eps) := by
    have e1 : (8 : ℝ) = ((8 : ℝ) ^ (1 / eps)) ^ eps := by
      rw [← Real.rpow_mul (by norm_num), one_div, inv_mul_cancel₀ heps.ne', Real.rpow_one]
    have e2 : ((8 : ℝ) ^ (1 / eps)) ^ eps ≤ x ^ eps :=
      Real.rpow_le_rpow (by positivity) (le_trans (le_max_right _ _) hx0) heps.le
    have e3 : x ^ eps ≤ x ^ (8 * eps) := Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith)
    linarith
  obtain ⟨⟨hn, -⟩, ⟨-, hm⟩, -⟩ := hW x hx i
  have hδ : (Fm.L x i).sc.delta1 ≤ 1 := by
    unfold Scale.delta1
    exact Real.rpow_le_one_of_one_le_of_nonpos (Fm.L x i).sc.one_lt_alt.le
      (by linarith [(Fm.L x i).sc.eps_pos])
  have hδ0 : 0 ≤ (Fm.L x i).sc.delta1 := by
    unfold Scale.delta1
    exact Real.rpow_nonneg (by linarith [(Fm.L x i).sc.one_lt_alt]) _
  have hm4 : (((Fm.D x i).R.m : ℕ) : ℝ) ^ 4 ≤ (((Fm.D x i).R.f : ℕ) : ℝ) := by
    have hs := Real.sq_sqrt (mul_nonneg hx0'.le hδ0)
    have hs0 := Real.sqrt_nonneg (x * (Fm.L x i).sc.delta1)
    have hm0 : (0 : ℝ) ≤ ((Fm.D x i).R.m : ℝ) := by positivity
    have hm2 : (((Fm.D x i).R.m : ℕ) : ℝ) ^ 2 ≤ 4 * x := by nlinarith
    have hm4' : (((Fm.D x i).R.m : ℕ) : ℝ) ^ 4 ≤ 16 * x ^ 2 := by nlinarith
    have hpow : x ^ ((2 : ℝ) + 8 * eps) = x ^ 2 * x ^ (8 * eps) := by
      rw [Real.rpow_add hx0', Real.rpow_two]
    have hf : (((Fm.D x i).R.f : ℕ) : ℝ) = 2 * ((Fm.D x i).R.n : ℝ) := by
      unfold Ranks.f
      push_cast
      ring
    rw [hf]
    have hx2 : 0 ≤ x ^ 2 := by positivity
    nlinarith
  refine ⟨⟨(Fm.D x i).R.two_le_m, (Fm.D x i).R.m_add_three_le_k, by exact_mod_cast hm4,
    (Fm.D x i).R.f_le_k⟩, ?_⟩
  show (FunData.Lc d.O : ℝ) ≤ (Fm.L x i).sc.b
  exact (lcLeOfCloud d.O (Fm.L x i).Sc (Fm.L x i).Sc_pos.le
    (fun τ j => cloudIcc (Fm.L x i) τ j)).trans (scLeB (Fm.params x hx i))
end GlobalTheory.BigTop.Fun.Close
end
end
