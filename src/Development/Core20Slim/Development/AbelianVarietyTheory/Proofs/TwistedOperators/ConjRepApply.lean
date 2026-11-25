module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.NodeAgree
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
public import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqExistsIffDsExists
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUniformRealThetaIntertwinerChainStep
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsItWOfGlobIt
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealThetaIntertwinerAdjointIsRealThetaIntertwine
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasInfExpIffHasInfQ
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjWeilDatumViaAdjointExchangedPair
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorsConjAdjointPullbackBijection
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianAdjointLawsStandardCharacter
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaHeisenbergConjugationNegHermitianSpace
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterInfinityExponentGroupLaws
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConjugateAdjointDagger
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HermitianOrthogonalExtensionData
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.MvPolynomial.Monad
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Chain.RealIt GlobalTheory.PairLift

noncomputable section

namespace GlobalTheory.AdjTr

variable {D : D7}

def conjRep {S T : HSp D} (ω : GlobalTheory.Grid.WRep S T) : GlobalTheory.Grid.WRep S T :=
  (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cjEnd (Equiv.refl (WO S T))).comp ω

theorem conjRep_apply {S T : HSp D} (ω : GlobalTheory.Grid.WRep S T) (p : GA D S × GA D T) (F : WO S T → ℂ) :
    conjRep ω p F = GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id (ω p (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id F)) := rfl

def adjRep {S T : HSp D} (ω : GlobalTheory.Grid.WRep S T) : GlobalTheory.Grid.WRep T S :=
  GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.conjAdjoint (conjRep ω)

theorem adjRep_apply {S T : HSp D} (ω : GlobalTheory.Grid.WRep S T) (h : GA D T) (g : GA D S) (F : WO T S → ℂ) :
    adjRep ω (h, g) F = fun y => ω (g, h) (fun x => F (adjO T S x)) (adjO S T y) := by
  funext y
  show starRingEnd ℂ (starRingEnd ℂ (ω (g, h) (fun x => starRingEnd ℂ (starRingEnd ℂ (F (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger S T x))))
    (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger T S y))) = _
  simp only [Complex.conj_conj, GlobalTheory.ConjAdjWeil.dagger_eq]


open GlobalTheory.FockAdjoint in
def swapHom {S T : HSp D} (A : Fr S) (B : Fr T) : PolF D T.rank S.rank →ₐ[ℂ] PolF D S.rank T.rank :=
  MvPolynomial.aeval fun v => MvPolynomial.C (sgv A B v.1 v.2.1 v.2.2) * MvPolynomial.X (v.1, v.2.2, v.2.1)


open GlobalTheory.FockAdjoint in
def swapInv {S T : HSp D} (A : Fr S) (B : Fr T) : PolF D S.rank T.rank →ₐ[ℂ] PolF D T.rank S.rank :=
  MvPolynomial.aeval fun v => MvPolynomial.C (sgv A B v.1 v.2.2 v.2.1) * MvPolynomial.X (v.1, v.2.2, v.2.1)

open GlobalTheory.FockAdjoint in
theorem swapHom_X {S T : HSp D} (A : Fr S) (B : Fr T) (v : FVar D T.rank S.rank) :
    swapHom A B (MvPolynomial.X v) = MvPolynomial.C (sgv A B v.1 v.2.1 v.2.2) * MvPolynomial.X (v.1, v.2.2, v.2.1) := by
  simp [swapHom]

open GlobalTheory.FockAdjoint in
theorem swapInv_X {S T : HSp D} (A : Fr S) (B : Fr T) (v : FVar D S.rank T.rank) :
    swapInv A B (MvPolynomial.X v) = MvPolynomial.C (sgv A B v.1 v.2.2 v.2.1) * MvPolynomial.X (v.1, v.2.2, v.2.1) := by
  simp [swapInv]


open GlobalTheory.FockAdjoint in
def swapEquiv {S T : HSp D} (A : Fr S) (B : Fr T) : PolF D T.rank S.rank ≃ₐ[ℂ] PolF D S.rank T.rank :=
  AlgEquiv.ofAlgHom (swapHom A B) (swapInv A B)
    (MvPolynomial.algHom_ext fun v => by
      rw [AlgHom.comp_apply, swapInv_X, map_mul, swapHom_X, MvPolynomial.algHom_C, AlgHom.id_apply]
      simp only [Algebra.algebraMap_eq_smul_one, ← mul_assoc]
      rw [← MvPolynomial.C_eq_smul_one, ← map_mul, sgv_mul_self, map_one, one_mul])
    (MvPolynomial.algHom_ext fun v => by
      rw [AlgHom.comp_apply, swapHom_X, map_mul, swapInv_X, MvPolynomial.algHom_C, AlgHom.id_apply]
      simp only [Algebra.algebraMap_eq_smul_one, ← mul_assoc]
      rw [← MvPolynomial.C_eq_smul_one, ← map_mul, sgv_mul_self, map_one, one_mul])

end GlobalTheory.AdjTr

end
