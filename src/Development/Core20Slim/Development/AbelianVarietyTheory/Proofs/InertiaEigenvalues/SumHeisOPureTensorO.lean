module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ParamsEx
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.Core20Slim.Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.PureTensorLIntertwine
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeisenbergOrientedFiniteFixesFockPolynomialVecto
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SobolevBoundedThetaFormMatrixCoeffSmooth
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.PureTensorOMulSource
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Classical
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Pi
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.LinearMap
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Empty
public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

noncomputable section

namespace GlobalTheory.FiniteHeisComb

variable {D : D7}

theorem heisO_aPlus (ψ : AddChar (AF D.host.F) ℂ) {θ : InfFam D} (hθ : IsInfFam θ) {S T : HSp D} {u : WO S T}
    (hu : u.map (infPart D) = 0) (τ : D.what₂.Tau)
    (J : Matrix (Fin T.rank) (Fin S.rank) ℂ → Matrix (Fin T.rank) (Fin S.rank) ℂ)
    (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (g : WO S T → ℂ) :
    heisO ψ S T u (aPlus (heisO ψ S T) θ τ J z g) = aPlus (heisO ψ S T) θ τ J z (heisO ψ S T u g) := by
  simp only [aPlus, crea]
  change GlobalTheory.Hk3.FiniteHeis.heisLin ψ S T u _ = _
  rw [map_smul, map_sub, map_smul]
  show _ • (heisO ψ S T u (Formalism.IndefR.Datum.dRho _ _ _ _ _) - _ • heisO ψ S T u (Formalism.IndefR.Datum.dRho _ _ _ _ _)) = _
  rw [GlobalTheory.Hk3.FiniteHeis.heisO_dRho ψ hθ hu, GlobalTheory.Hk3.FiniteHeis.heisO_dRho ψ hθ hu]

theorem aPlus_sum {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {θ : InfFam D} (hθ : IsInfFam θ)
    {S T : HSp D} (τ : D.what₂.Tau)
    (J : Matrix (Fin T.rank) (Fin S.rank) ℂ → Matrix (Fin T.rank) (Fin S.rank) ℂ)
    (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (c : WO S T → ℂ) {g : WO S T → ℂ} (hg : IsThetaFunO ψ S T g)
    (s : Finset (WO S T)) :
    IsThetaFunO ψ S T (∑ u ∈ s, c u • heisO ψ S T u g) ∧
      aPlus (heisO ψ S T) θ τ J z (∑ u ∈ s, c u • heisO ψ S T u g) =
        ∑ u ∈ s, c u • aPlus (heisO ψ S T) θ τ J z (heisO ψ S T u g) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨by simpa using (GlobalTheory.OrientedHeis.theta_zero : IsThetaFunO ψ S T 0), ?_⟩
    have e := GlobalTheory.AdTh.SourceBasis.aPlus_smul hψ hθ τ J z 0 (GlobalTheory.OrientedHeis.theta_zero (ψ := ψ) (S := S) (T := T))
    simpa using e
  | insert a s ha ih =>
    have ht : IsThetaFunO ψ S T (c a • heisO ψ S T a g) :=
      GlobalTheory.OrientedHeis.theta_smul _ (GlobalTheory.Unf.MatCoef.theta_heisO_any hψ hθ hg a)
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    refine ⟨GlobalTheory.OrientedHeis.theta_add ht ih.1, ?_⟩
    rw [GlobalTheory.AdTh.SourceBasis.aPlus_add hψ hθ τ J z ht ih.1, ih.2,
      GlobalTheory.AdTh.SourceBasis.aPlus_smul hψ hθ τ J z _ (GlobalTheory.Unf.MatCoef.theta_heisO_any hψ hθ hg a)]

theorem sum_heisO_pureTensorO : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D), IsStdChar D ψ (-1) → IsInfFam θ → ∀ (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (c : WO S T →₀ ℂ), (∀ u ∈ c.support, u.map (infPart D) = 0) → ∀ x : WO S T → ℂ, IsThetaFunO ψ S T x → ∀ P : MvPolynomial (FVar D T.rank S.rank) ℂ, (c.sum fun u z => z • heisO ψ S T u (pureTensorO ψ θ S T sS sT BS BT x P)) = pureTensorO ψ θ S T sS sT BS BT (c.sum fun u z => z • heisO ψ S T u x) P := by
  intro D ψ θ S T hψ hθ sS BS sT BT c hc x hx P
  let Φ : Module.End ℂ (WO S T → ℂ) := c.sum fun u z => z • GlobalTheory.Hk3.FiniteHeis.heisLin ψ S T u
  have hΦ : ∀ g, Φ g = c.sum fun u z => z • heisO ψ S T u g := by
    intro g
    simp only [Φ, Finsupp.sum]
    rw [LinearMap.sum_apply]
    rfl
  have h := (GlobalTheory.OrientedHeis.pureTensorL_intertwine (IsThetaFunO ψ S T) GlobalTheory.OrientedHeis.theta_zero
    (fun _ _ ha hb => GlobalTheory.OrientedHeis.theta_add ha hb) (fun a _ h => GlobalTheory.OrientedHeis.theta_smul a h)
    (aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT)
    (aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT) Φ
    (fun k g hg => ⟨?_, ?_⟩) x hx P).2
  · rw [hΦ, hΦ] at h
    exact h
  · exact GlobalTheory.AdTh.SourceBasis.aPlus_th hψ hθ _ _ _ hg
  · obtain ⟨τ, i, j⟩ := k
    simp only [aPlusAll]
    rw [hΦ, hΦ, Finsupp.sum, Finsupp.sum, (aPlus_sum hψ hθ τ _ _ c hg c.support).2]
    refine Finset.sum_congr rfl fun u hu => ?_
    rw [heisO_aPlus ψ hθ (hc u hu)]

end GlobalTheory.FiniteHeisComb
