module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetOperatorRationalFormConjEqConjTable
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbLLMem
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairIntAt
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.HighestWeightBelow
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TaylorCoeffConjugateSeriesStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaNormBoundHypothesesSatisfiedStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeUnitNormSqNonneg
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralJAndAlgebraicData
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaVacuaConjugatesCmPoints
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockVacEqJets
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTwoTorsionCMPointAllConjugates
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousCoeffBlockAct
public import Formalism.LocalRingCardinality.DataCoeff
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Formalism.LocalToGlobal.KernelLattices.ThDistC
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Init.Data.Rat.Basic
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.CharP.IntermediateField
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.SumSize GlobalTheory.KerConjMean
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jetOperator_rationalForm_conj_eq_conjTable : ∀ {D : D7} {a b : ℕ} (lam : D.what₂.Tau → DomWeight a) (lam' : D.what₂.Tau → DomWeight b) (n : D.what₂.Tau → ℕ)
    (J : (Formalism.L2.Ker.DVar D.what₂.Tau a b →₀ ℕ) → ℂ) (σ : D.what₂.LL →+* ℂ) (ρ' : Qbar →ₐ[ℚ] ℂ)
    (f : VV D.what₂.LL lam →ₗ[D.what₂.LL] VV D.what₂.LL lam'), Formalism.L2.Ker.JetInVV ℂ lam lam' n → (∀ m, J m ∈ Qbar) →
    (∀ x, Formalism.MainNotions.StandardLatticesGL3.cj Qbar ρ' (D.what₂.embLL x) = σ x) →
    (∀ u, Formalism.L2.Ker.jetOp lam lam' J n (GlobalTheory.CoefModel.mapVV D.what₂.embLL lam u) = GlobalTheory.CoefModel.mapVV D.what₂.embLL lam' (f u)) →
    ∀ u, GlobalTheory.CoefModel.mapVV σ lam' (f u) =
      Formalism.L2.Ker.jetOp lam lam' (fun m => Formalism.MainNotions.StandardLatticesGL3.cj Qbar ρ' (J m)) n (GlobalTheory.CoefModel.mapVV σ lam u) := by
  first | exact @GlobalTheory.JetDescent.mapVV_rational_form_conj | exact GlobalTheory.JetDescent.mapVV_rational_form_conj | (intros; apply GlobalTheory.JetDescent.mapVV_rational_form_conj <;> assumption)
