module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingInl
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ImportsBis
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDblCoordDblD
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaDiagInt
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledGramSatisfiesXiRelation
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThetaFunctionThetaTransformRationalDarbouxStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelWeilSectionDegeneratePrincipalSeriesLaw
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsGLSubmatrix
public import Development.AbelianVarietyTheory.Definitions.Foundations.MemSiegelOfIffRightAct
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.SatakeDualWeyl.Statement
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Algebra.Ring.Units
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.DiagThetaRule

open GlobalTheory.Doubling Formalism.IndefR.Datum

theorem JR_dblSp_gram {D : D7} (S : HSp D) :
    JR (F := D.host.F) (AF D.host.F) (dblSp S).gram =
      blkMat finSumFinEquiv (JR (F := D.host.F) (AF D.host.F) S.gram) (-(JR (F := D.host.F) (AF D.host.F) S.gram)) := by
  rw [show (dblSp S).gram = dblGram finSumFinEquiv S.gram from gram_hdbl S, dblGram, JR,
    blkMat_map _ _ (map_zero _)]
  simp [JR, Matrix.map_neg]

theorem neg_one_mem_UJ {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] (σ : A →+* A)
    (J : Matrix n n A) : (-1 : GL n A) ∈ Formalism.UG.UJ σ J := by
  show Formalism.UG.cT σ (-1 : GL n A).val * J * (-1 : GL n A).val = J
  rw [Units.val_neg, Units.val_one, Formalism.UG.cT, Matrix.map_neg _ (map_neg σ), Matrix.map_one _ (map_zero σ) (map_one σ),
    Matrix.transpose_neg, Matrix.transpose_one, Matrix.neg_mul, Matrix.one_mul, Matrix.mul_neg, Matrix.mul_one, neg_neg]

def epsPair {D : D7} (S : HSp D) : GL (Fin S.rank) (AE D) × GL (Fin S.rank) (AE D) := (1, -1)

theorem blkGL_epsPair_mem {D : D7} (S : HSp D) :
    blkGL finSumFinEquiv (epsPair S) ∈
      Formalism.UG.UJ (sigR (AF D.host.F) D.sp.cm.sig) (JR (F := D.host.F) (AF D.host.F) (dblSp S).gram) := by
  rw [JR_dblSp_gram, epsPair, blkGL_mem_UJ]
  exact ⟨one_mem _, neg_one_mem_UJ _ _⟩

def epsD {D : D7} (S : HSp D) : GA D (dblSp S) := ⟨blkGL finSumFinEquiv (epsPair S), blkGL_epsPair_mem S⟩

theorem mt_epsD {D : D7} (S : HSp D) :
    Formalism.L2.Theta.mt (dblSp S) (epsD S) =
      blkMat finSumFinEquiv (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) (-1) := rfl

end GlobalTheory.DiagThetaRule
