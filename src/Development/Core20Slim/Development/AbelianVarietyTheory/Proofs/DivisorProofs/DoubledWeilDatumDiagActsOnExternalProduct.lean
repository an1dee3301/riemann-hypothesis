module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingInl
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ImportsBis
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousUgReindex
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawOneSourceOrthogonalSumTargets
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaHeisenbergConjugationNegHermitianSpace
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridHeckeCharactersExist
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConjugateAdjointDagger
public import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsGLSubmatrix
public import Development.AbelianVarietyTheory.Definitions.Foundations.MemSiegelOfIffRightAct
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ContinuousResTSymm
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsBiThetaIffJoin
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaTensorRuleTargetOrthogonalSum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsEtaTildeUnramified
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilDatumOfSplittingCharacters
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExternalProductOnHermitianSumSmulLeft
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasChr
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Basic
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Hom.Instances
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Block
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.DblRestrictChar

open Formalism.IndefR.Datum


set_option maxHeartbeats 1000000 in
theorem dbl_diag_box : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
      (ω : GA D S × GA D T →* Module.End ℂ (Formalism.IndefR.Datum.WO S T → ℂ)),
      Formalism.IndefR.Datum.IsWeilDatumO ψ S T χS χT ω →
      ∀ ωd : GA D S × GA D (GlobalTheory.Doubling.dblSp T) →* Module.End ℂ (Formalism.IndefR.Datum.WO S (GlobalTheory.Doubling.dblSp T) → ℂ),
        Formalism.IndefR.Datum.IsWeilDatumO ψ S (GlobalTheory.Doubling.dblSp T) χS 1 ωd →
        (∀ (h : GA D T) (hd : GA D (GlobalTheory.Doubling.dblSp T)),
          Formalism.L2.Theta.mt (GlobalTheory.Doubling.dblSp T) hd =
            Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks (Formalism.L2.Theta.mt T h) 0 0 1) →
          ∃ c : ℂ, ∀ f₁ f₂ : Formalism.IndefR.Datum.WO S T → ℂ,
            Formalism.IndefR.Datum.IsThetaFunO ψ S T f₁ → Formalism.IndefR.Datum.IsThetaFunO ψ S T f₂ →
              ωd (1, hd) (fun w : Formalism.IndefR.Datum.WO S (GlobalTheory.Doubling.dblSp T) => f₁ (w.submatrix (finSumFinEquiv ∘ Sum.inl) id) * star (f₂ (w.submatrix (finSumFinEquiv ∘ Sum.inr) id))) = c • (fun w : Formalism.IndefR.Datum.WO S (GlobalTheory.Doubling.dblSp T) => ω (1, h) f₁ (w.submatrix (finSumFinEquiv ∘ Sum.inl) id) * star (f₂ (w.submatrix (finSumFinEquiv ∘ Sum.inr) id)))) →
        ∀ (h : GA D T) (hd : GA D (GlobalTheory.Doubling.dblSp T)),
          Formalism.L2.Theta.mt (GlobalTheory.Doubling.dblSp T) hd =
            Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks (Formalism.L2.Theta.mt T h) 0 0 1) →
          ∀ f₁ f₂ : Formalism.IndefR.Datum.WO S T → ℂ,
            Formalism.IndefR.Datum.IsThetaFunO ψ S T f₁ → Formalism.IndefR.Datum.IsThetaFunO ψ S T f₂ →
              ωd (1, hd) (fun w : Formalism.IndefR.Datum.WO S (GlobalTheory.Doubling.dblSp T) => f₁ (w.submatrix (finSumFinEquiv ∘ Sum.inl) id) * star (f₂ (w.submatrix (finSumFinEquiv ∘ Sum.inr) id))) = (fun w : Formalism.IndefR.Datum.WO S (GlobalTheory.Doubling.dblSp T) => ω (1, h) f₁ (w.submatrix (finSumFinEquiv ∘ Sum.inl) id) * star (f₂ (w.submatrix (finSumFinEquiv ∘ Sum.inr) id))) := by
  intro D ψ hψ S T χS χT ω hω ωd hωd _ h hd hhd f₁ f₂ hf₁ hf₂
  obtain ⟨ωB, hB⟩ := GlobalTheory.WeilExist.exists_isWeilDatumO D ψ hψ S (GlobalTheory.ChiGrid.negSp T) χS χT⁻¹
    (GlobalTheory.WeilParts.exists_isEtaTilde_unramified D) hω.hecS (GlobalTheory.HeckeCharsOfSquare.isHeckeChar_inv hω.hecT) hω.resS
    (resEta_inv hω.resT)
  let d := GlobalTheory.BiTransfer.sumDec T (GlobalTheory.ChiGrid.negSp T)
  have hωd' : IsWeilDatumO ψ S (GlobalTheory.Doubling.hsum T (GlobalTheory.ChiGrid.negSp T)) χS (χT * χT⁻¹) ωd := by
    rw [mul_inv_cancel]; exact hωd
  have key := (GlobalTheory.TensorTargetRule.tensorTarget D ψ hψ _ T (GlobalTheory.ChiGrid.negSp T) d S).om_box χS χT χT⁻¹ ωd ω ωB
    hωd' hω hB 1 h 1 f₁ (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id f₂) hf₁ (GlobalTheory.CjNeg.theta_negT hψ hf₂)
  have e1 : d.emb (h, 1) = hd := by
    apply GlobalTheory.MixModel.mt_injective (GlobalTheory.Doubling.hsum T (GlobalTheory.ChiGrid.negSp T))
    rw [GlobalTheory.SeesawSumTarget.emb_sumDec, GlobalTheory.SquareComm.mt_blk]
    refine Eq.trans ?_ hhd.symm
    rw [GlobalTheory.Doubling.blkMat, Matrix.reindex_apply, GlobalTheory.AdelicLatMove.mt_one]
  have e2 : ωB ((1 : GA D S), (1 : GA D (GlobalTheory.ChiGrid.negSp T))) = 1 := map_one ωB
  rw [e1, e2, Module.End.one_apply, GlobalTheory.SeesawSumTarget.boxT_sumDec, GlobalTheory.SeesawSumTarget.boxT_sumDec] at key
  exact key

end GlobalTheory.DblRestrictChar
