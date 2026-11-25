module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfiniteTensorBound
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
public import Development.Core20Slim.Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.LocalCharacterPowerConductorBound
public import Development.Core20Slim.Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ArchimedeanTensorFactorUnfolding
public import Development.Core20Slim.Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ArchimedeanTensorVolumeCoefficient
public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
public import Development.Core20Slim.Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.MemHalfCosetSelf
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceSzNonneg
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
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.LinearOrder
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

section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
namespace GlobalTheory.ArchTens
attribute [local instance] Formalism.BasicNotions.Host.cmStar
end GlobalTheory.ArchTens
open GlobalTheory.ArchTens in
theorem _root_.GlobalTheory.SumSize.archimedean_tensor_size_bound_of_local (hP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) : InfTensK := by
  obtain ⟨F1, h1⟩ := _root_.GlobalTheory.T.local_character_power_conductor_bound hP
  obtain ⟨F2, h2⟩ := _root_.GlobalTheory.T.archimedean_tensor_factor_unfolding hP
  obtain ⟨F3, h3⟩ := _root_.GlobalTheory.T.archimedean_tensor_volume_bound hP
  refine ⟨max F1 (max F2 F3), fun CF hCF => ?_⟩
  obtain ⟨C1, h1⟩ := h1 CF (le_trans (le_max_left _ _) hCF)
  obtain ⟨C2, h2⟩ := h2 CF (le_trans ((le_max_left _ _).trans (le_max_right _ _)) hCF)
  obtain ⟨C3, h3⟩ := h3 CF (le_trans ((le_max_right _ _).trans (le_max_right _ _)) hCF)
  refine ⟨max (max (4 * C1) (2 * C2)) (max (2 * C3) 0), fun ε C hC => ?_⟩
  have hC1 : C1 ≤ C / 2 / 2 := by have := (le_max_left _ _).trans ((le_max_left _ _).trans hC); linarith
  have hC2 : C2 ≤ C / 2 := by have := (le_max_right _ _).trans ((le_max_left _ _).trans hC); linarith
  have hC3 : C3 ≤ C / 2 := by have := (le_max_left _ _).trans ((le_max_right _ _).trans hC); linarith
  have hC0 : 0 ≤ C := (le_max_right _ _).trans ((le_max_right _ _).trans hC)
  obtain ⟨x1, h1⟩ := h1 ε (C / 2 / 2) hC1
  obtain ⟨x2, h2⟩ := h2 ε (C / 2) hC2
  obtain ⟨x3, h3⟩ := h3 ε (C / 2) hC3
  refine ⟨max x1 (max x2 x3), ?_⟩
  intro D large₂ he hx Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hIs hAt hF
  exact infTensAt_of_places ch hC0
    (h2 D large₂ he (((le_max_left _ _).trans (le_max_right _ _)).trans hx) Γ Pl0 T A Ks R F hS ch hIs hAt hF
      (h1 D large₂ he ((le_max_left _ _).trans hx) Γ Pl0 T A Ks R F hS ch hIs hAt hF))
    (h3 D large₂ he (((le_max_right _ _).trans (le_max_right _ _)).trans hx) Γ Pl0 T A Ks R F hS ch hIs hAt hF)
end
end

section
open GlobalTheory.SumSize GlobalTheory.RowClaim
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_size_archimedean_tensor_bound : _root_.GlobalTheory.FunPr.ThetaLocalInputs → InfTensK := by
  first | exact @_root_.GlobalTheory.SumSize.archimedean_tensor_size_bound_of_local | exact _root_.GlobalTheory.SumSize.archimedean_tensor_size_bound_of_local | (intros; apply _root_.GlobalTheory.SumSize.archimedean_tensor_size_bound_of_local <;> assumption)
end
