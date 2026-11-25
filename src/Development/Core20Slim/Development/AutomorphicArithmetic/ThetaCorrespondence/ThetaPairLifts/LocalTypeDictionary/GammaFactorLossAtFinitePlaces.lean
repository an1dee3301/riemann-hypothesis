module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteGammaBound
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
public import Development.Core20Slim.Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.MemHalfCosetSelf
public import Development.Core20Slim.Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Formalism.LocalRingCardinality.DataParams₂
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.Divisibility.LiftLat
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Group.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

section
open NumberField
namespace GlobalTheory.GamLoss
variable {E : Type} [Field E] [NumberField E]
end GlobalTheory.GamLoss
namespace GlobalTheory.GamLoss
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FunObj
variable {D : D7}
end GlobalTheory.GamLoss
namespace GlobalTheory.GamLoss
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)
variable {D : D7}
end GlobalTheory.GamLoss
namespace GlobalTheory.GamLoss
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SumSize GlobalTheory.RowTest
open Formalism.DivisionValues (vw lw)
variable {D : D7}
end GlobalTheory.GamLoss
namespace GlobalTheory.GamLoss
open GlobalTheory.SumSize GlobalTheory.RowClaim
theorem finite_place_gamma_loss_bound : FunPr.ThetaLocalInputs → FinGamK := by
  intro _
  refine ⟨0, fun CF _ => ⟨90, fun ε C hC => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F _ ch _ _ _ => ?_⟩⟩⟩
  have hL : (1 : ℝ) ≤ large₂.sc.L := Real.one_le_rpow large₂.sc.one_lt_alt.le large₂.sc.eps_pos.le
  have hb : (1 : ℝ) ≤ large₂.sc.b := Real.one_le_exp (by linarith)
  have hlb : (1 : ℝ) ≤ Real.log large₂.sc.b := by
    show (1 : ℝ) ≤ Real.log (Real.exp large₂.sc.L)
    rw [Real.log_exp]; exact hL
  exact finGamAt_of ch hC hb hlb
end GlobalTheory.GamLoss
end

section
open GlobalTheory.SumSize GlobalTheory.RowClaim
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gamma_factor_loss_at_finite_places : _root_.GlobalTheory.FunPr.ThetaLocalInputs → FinGamK := by
  first | exact @_root_.GlobalTheory.GamLoss.finite_place_gamma_loss_bound | exact _root_.GlobalTheory.GamLoss.finite_place_gamma_loss_bound | (intros; apply _root_.GlobalTheory.GamLoss.finite_place_gamma_loss_bound <;> assumption)
end
