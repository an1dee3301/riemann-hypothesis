module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.DictionaryDepthPairStandard
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
public import Development.Core20Slim.Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ConjTopAtOfRankLeOfWeightLe
public import Development.Core20Slim.Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ConjugateRowBoundOfDictionary
public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjPlInvolutive
public import Development.AbelianVarietyTheory.Definitions.Divisors.InvVolConjLevelOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.MemHalfCosetSelf
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbLLMem
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbeddingsCurveFieldAboveFiniteNonemptyStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConstMeanLogAreaLogThetaNormLe
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfiniteTopOfDictionaryDepth
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.NrmOneNonneg
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.OppositeKernelsRationalRowMapLargeConstantsStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalEqualSignKernelsLargeConstantsStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.Core20Slim.Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
public import Development.Core20Slim.Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataParams₂
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.Divisibility.LiftLat
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.PairingDivisors.StatementH
public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
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
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
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
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.SumSize GlobalTheory.KerConjMean GlobalTheory.SumSize.OppConj
namespace GlobalTheory.KerConjMean
attribute [local instance] Formalism.BasicNotions.Host.cmStar
section Std
variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R)
end Std
theorem kernel_conj_mean_pairing_standard_KType : FunPr.ThetaLocalInputs → (∀ D, NormSum.Inp D) → DictK → DepthK → PairStdK := by
  intro hP hI hD hDp
  obtain ⟨C1, hC1, hmean⟩ := GlobalTheory.T.exists_const_mean_logArea_logThetaNorm_le
  obtain ⟨F1, k1⟩ := _root_.GlobalTheory.T.kernel_conjugation_average hP hI hD hDp C1 hC1
  obtain ⟨F2, k2⟩ := GlobalTheory.T.rationalEqualSignKernels_largeConstants
  obtain ⟨F3, k3⟩ := _root_.GlobalTheory.T.conjRowAt_of_dict_depth hP hI hD hDp C1 hC1
  obtain ⟨F4, k4⟩ := GlobalTheory.T.oppositeKernelsRationalRowMap_largeConstants
  refine ⟨max (max F1 F2) (max F3 F4), fun CF hCF => ?_⟩
  obtain ⟨C01, l1⟩ := k1 CF (by simp only [max_le_iff] at hCF; exact hCF.1.1)
  obtain ⟨C02, l2⟩ := k2 CF (by simp only [max_le_iff] at hCF; exact hCF.1.2)
  obtain ⟨C03, l3⟩ := k3 CF (by simp only [max_le_iff] at hCF; exact hCF.2.1)
  obtain ⟨C04, l4⟩ := k4 CF (by simp only [max_le_iff] at hCF; exact hCF.2.2)
  refine ⟨2 * max (max C01 C02) (max C03 C04), fun ε C hC => ?_⟩
  have hC' : max (max C01 C02) (max C03 C04) ≤ C / 2 := by linarith
  simp only [max_le_iff] at hC'
  obtain ⟨x1, m1⟩ := l1 ε (C / 2) hC'.1.1
  obtain ⟨x2, m2⟩ := l2 ε (C / 2) hC'.1.2
  obtain ⟨x3, m3⟩ := l3 ε (C / 2) hC'.2.1
  obtain ⟨x4, m4⟩ := l4 ε (C / 2) hC'.2.2
  refine ⟨max (max x1 x2) (max x3 x4), fun D large₂ hε hx Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hIs hAt hF => ?_⟩
  simp only [max_le_iff] at hx
  obtain ⟨hL1, hLrd, hLd⟩ := sizes D large₂ Γ Pl0 T A Ks R F hS
  obtain ⟨hmA, hmT⟩ := hmean D (hI D) ch.S.Z.δ ch.S.Z.t0 ch.S.Z.crv ch.S.Z.pt0 _ hL1 hLrd hLd
  exact pairStdAt_of ch C large₂.sc.b C1 hmA hmT
    (fun σ => GlobalTheory.T.embeddingsCurveFieldAbove_finite_nonempty D (hI D) ch.S.Z.δ ch.S.Z.t0 ch.S.Z.crv ch.S.Z.pt0 σ)
    (m2 D large₂ hε hx.1.2 Γ Pl0 T A Ks R F hS ch hIs hAt hF)
    (m1 D large₂ hε hx.1.1 Γ Pl0 T A Ks R F hS ch hIs hAt hF)
    (m4 D large₂ hε hx.2.2 Γ Pl0 T A Ks R F hS ch hIs hAt hF)
    (m3 D large₂ hε hx.2.1 Γ Pl0 T A Ks R F hS ch hIs hAt hF)
end GlobalTheory.KerConjMean
end
end

section
open GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.SumSize.OppConj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conj_mean_kernel_pairing : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → DictK → DepthK → PairStdK := by
  first | exact @_root_.GlobalTheory.KerConjMean.kernel_conj_mean_pairing_standard_KType | exact _root_.GlobalTheory.KerConjMean.kernel_conj_mean_pairing_standard_KType | (intros; apply _root_.GlobalTheory.KerConjMean.kernel_conj_mean_pairing_standard_KType <;> assumption)
end
