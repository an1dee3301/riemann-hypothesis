module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingInl
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ImportsBis
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilDatumTransportAdelicSchwartzThetaTransStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledUnitaryPartnerDiagStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportedWeilDatumKeepsAdmissibleFormsStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportedWeilDatumIsUnitaryAdelicSchwartzStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousTransportedWeilDatumAdelicSchwartzStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousUgReindex
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelRuleTransportedWeilDatumDoubledTargetStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportedWeilDatumDoubledTargetRestrictBoxTensStatement
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsGLSubmatrix
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Prod
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Block
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Instances.Matrix

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.WeilSchrodinger.DblTarget

set_option maxHeartbeats 1000000

theorem exists_dbl_target : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (χS χT : (AE D)ˣ →* Circle), IsHeckeChar D χS → IsHeckeChar D χT →
      ResEta D χS S.rank → ResEta D χT T.rank →
      ∀ (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
        (ξ : AF D.host.F ⊗[D.host.F] D.host.E), JA = T.gramᵀ →
        ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
        ∀ (κ : Type) [Fintype κ]
          (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
          (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
            co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
          ∀ ω : GA D S × GA D T →* Module.End ℂ (Formalism.IndefR.Datum.WO S T → ℂ),
            Formalism.IndefR.Datum.IsWeilDatumO ψ S T χS χT ω →
 ∀ om : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA) ×
      GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB) →* Module.End ℂ ((κ → AF D.host.F) → ℂ),
                       GlobalTheory.WeilSchrodinger.IsTransport ψ co ω om →
                       ∃ (dd : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JB)
                           (GlobalTheory.WeilM.dbl (incM D.host.F JA))) (κ ⊕ κ))
                         (omd : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (GlobalTheory.WeilM.dbl (incM D.host.F JA)) →*
                           Module.End ℂ ((κ ⊕ κ → AF D.host.F) → ℂ)),
                         GlobalTheory.WeilM.IsDblCoord (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JB) (incM D.host.F JA)
                           (GlobalTheory.WeilSchrodinger.transD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) co) dd ∧
                         GlobalTheory.WeilM.IsUWeilSplit (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (GlobalTheory.WeilM.adeleClass D.host.F) ψ ξ
                           (incM D.host.F JB) (GlobalTheory.WeilM.dbl (incM D.host.F JA)) dd χS (GlobalTheory.WeilM.diagCols (Fin T.rank)) omd ∧
                         ∀ (g : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA))
                           (gd : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (GlobalTheory.WeilM.dbl (incM D.host.F JA))),
                           gd.1.1 = Matrix.fromBlocks g.1.1 0 0 1 →
                           ∀ φ₁ ∈ GlobalTheory.WeilM.schA D.host.F κ, ∀ φ₂ ∈ GlobalTheory.WeilM.schA D.host.F κ,
                             omd gd (GlobalTheory.WeilM.boxFun φ₁ φ₂) = GlobalTheory.WeilM.boxFun (om (g, 1) φ₁) φ₂ := by
  intro D ψ hψ S T χS χT hS hT rS rT JA JB ξ hA hB κ _ co hrat ω hω om hom
  have h1S := isHeckeChar_one (D := D)
  have r1 := resEta_one_dblSp T rT
  obtain ⟨ωd, hωd⟩ := GlobalTheory.weilRepresentationUnitaryPair D ψ S (GlobalTheory.Doubling.dblSp T) χS 1 hψ hS h1S rS r1
  have hrat' := coDbl_rat hA co hrat
  obtain ⟨omp, hmp⟩ := GlobalTheory.T.exists_weilDatum_transport_adelicSchwartz_thetaTransform D ψ hψ S (GlobalTheory.Doubling.dblSp T) χS 1 hS h1S rS r1 _ JB ξ rfl hB (κ ⊕ κ)
    (coDbl hA co) hrat' ωd hωd
  have h2 := GlobalTheory.T.transportedWeil_preserves_schwartz_heisenberg_equivariant D ψ hψ S (GlobalTheory.Doubling.dblSp T) χS 1 hS h1S rS r1 _ JB ξ rfl hB (κ ⊕ κ)
    (coDbl hA co) hrat' ωd hωd omp hmp
  have h3 := GlobalTheory.T.transportedWeilDatum_keeps_admissible_forms D ψ hψ S (GlobalTheory.Doubling.dblSp T) χS 1 hS h1S rS r1 _ JB ξ rfl hB (κ ⊕ κ)
    (coDbl hA co) hrat' ωd hωd omp hmp
  have h4 := GlobalTheory.T.transportedWeilDatum_isUnitary_adelicSchwartz D ψ hψ S (GlobalTheory.Doubling.dblSp T) χS 1 hS h1S rS r1 _ JB ξ rfl hB (κ ⊕ κ)
    (coDbl hA co) hrat' ωd hωd omp hmp
  have h5 := GlobalTheory.T.continuous_transported_weilDatum_adelicSchwartz D ψ hψ S (GlobalTheory.Doubling.dblSp T) χS 1 hS h1S rS r1 _ JB ξ rfl hB (κ ⊕ κ)
    (coDbl hA co) hrat' ωd hωd omp hmp
  have hsp : GlobalTheory.WeilM.IsUSplitting (GlobalTheory.WeilM.adeleClass D.host.F) ψ (coDbl hA co)
      (GlobalTheory.WeilM.actAB (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig)) omp := ⟨⟨h2.1, h2.2, h3⟩, h4, h5⟩
  have hsg := GlobalTheory.T.siegelRule_transported_weilDatum_doubledTarget D ψ hψ S T χS hS rS JB ξ hB (κ ⊕ κ) (coDbl hA co) hrat' ωd hωd omp hmp
  have t1 := isDblCoord_transD co
  have t2 : GlobalTheory.WeilM.IsLagr (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (GlobalTheory.WeilM.dbl (incM D.host.F JA))
      (GlobalTheory.WeilM.diagCols (Fin T.rank)) := GlobalTheory.WeilM.isLagr_diagCols _ _
  have t4 : GlobalTheory.WeilM.IsUSplitting (GlobalTheory.WeilM.adeleClass D.host.F) ψ (transD _ (dblRows co)) (GlobalTheory.WeilM.actB _)
      ((omp.comp (MonoidHom.inl _ _)).comp (ugDbl T hA)) :=
    isUSplitting_reindex finSumFinEquiv (dblRows co) _ (reindex_dbl_incM T hA) (isUSplitting_inl hsp)
  have t5 : GlobalTheory.WeilM.SiegelRule _ (GlobalTheory.WeilM.adeleClass D.host.F) ψ ξ (incM D.host.F JB) _ (transD _ (dblRows co)) χS
      (GlobalTheory.WeilM.diagCols (Fin T.rank)) ((omp.comp (MonoidHom.inl _ _)).comp (ugDbl T hA)) :=
    siegelRule_reindex finSumFinEquiv (dblRows co) _ (reindex_dbl_incM T hA) χS _ hsg
  refine ⟨_, _, t1, ⟨t2, t4, t5⟩, ?_⟩
  intro g gd hgd φ₁ hφ₁ φ₂ hφ₂
  have key := GlobalTheory.T.transportedWeilDatum_doubledTarget_restrict_boxTensor D ψ hψ S T χS χT hS hT rS rT JA JB ξ hA hB κ co hrat ω hω om hom ωd hωd omp hmp
    g (ugDbl T hA gd) (by rw [ugDbl_coe, hgd]) φ₁ hφ₁ φ₂ hφ₂
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply, MonoidHom.inl_apply]
  exact key

end GlobalTheory.WeilSchrodinger.DblTarget

end
