module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingInl
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ImportsBis
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousUgReindex
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActOOneOne
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaFunctionScalarProductPreservedIsometry
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThetaFunDoubledSpaceBoxProductStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledSpaceBoxProductInnerFactorizesStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFunFamiliesSameHeisenbergInnerEqSmulStatement
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsGLSubmatrix
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisThetaLaws
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
public import Init.Data.Function
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Block
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.Instances.Matrix

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasMat GlobalTheory.SplitWeil.matrixMeasurableSpace
open Formalism.IndefR.Datum

noncomputable section

namespace GlobalTheory.DblThetaRestrict

open Formalism.IndefR.Datum GlobalTheory.DblBox MeasureTheory

theorem scalar : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
      (ω : GA D S × GA D T →* Module.End ℂ (Formalism.IndefR.Datum.WO S T → ℂ)),
      Formalism.IndefR.Datum.IsWeilDatumO ψ S T χS χT ω →
      ∀ ωd : GA D S × GA D (GlobalTheory.Doubling.dblSp T) →* Module.End ℂ (Formalism.IndefR.Datum.WO S (GlobalTheory.Doubling.dblSp T) → ℂ),
        Formalism.IndefR.Datum.IsWeilDatumO ψ S (GlobalTheory.Doubling.dblSp T) χS 1 ωd →
        ∀ (h : GA D T) (hd : GA D (GlobalTheory.Doubling.dblSp T)),
          Formalism.L2.Theta.mt (GlobalTheory.Doubling.dblSp T) hd =
            Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks (Formalism.L2.Theta.mt T h) 0 0 1) →
          ∃ c : ℂ, ∀ f₁ f₂ : Formalism.IndefR.Datum.WO S T → ℂ,
            Formalism.IndefR.Datum.IsThetaFunO ψ S T f₁ → Formalism.IndefR.Datum.IsThetaFunO ψ S T f₂ →
              ωd (1, hd) (fun w : Formalism.IndefR.Datum.WO S (GlobalTheory.Doubling.dblSp T) => f₁ (w.submatrix (finSumFinEquiv ∘ Sum.inl) id) * star (f₂ (w.submatrix (finSumFinEquiv ∘ Sum.inr) id))) = c • (fun w : Formalism.IndefR.Datum.WO S (GlobalTheory.Doubling.dblSp T) => ω (1, h) f₁ (w.submatrix (finSumFinEquiv ∘ Sum.inl) id) * star (f₂ (w.submatrix (finSumFinEquiv ∘ Sum.inr) id))) := by
  intro D ψ hψ S T χS χT ω hω ωd hωd h hd hh
  have hθ := GlobalTheory.T.isThetaFun_doubledSpaceBoxProduct D ψ hψ S
  have hH := (GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ S T).1
  let ι : Type := {p : (WO S T → ℂ) × (WO S T → ℂ) // IsThetaFunO ψ S T p.1 ∧ IsThetaFunO ψ S T p.2}
  let X : ι → WO S (GlobalTheory.Doubling.dblSp T) → ℂ := fun p => ωd (1, hd) (box p.1.1 p.1.2)
  let Y : ι → WO S (GlobalTheory.Doubling.dblSp T) → ℂ := fun p => box (ω (1, h) p.1.1) p.1.2
  let act : WO S (GlobalTheory.Doubling.dblSp T) → ι → ι := fun w p =>
    ⟨(heisO ψ S T (top w) p.1.1, heisO ψ S T (bot w) p.1.2), hH _ _ p.2.1, hH _ _ p.2.2⟩
  let g : WO S (GlobalTheory.Doubling.dblSp T) → WO S (GlobalTheory.Doubling.dblSp T) := actO S (GlobalTheory.Doubling.dblSp T) 1 hd
  have hg : Function.Surjective g := fun y => ⟨actO S (GlobalTheory.Doubling.dblSp T) 1 hd⁻¹ y, by
    simp only [g, actO, inv_one, show Formalism.L2.Theta.mt S 1 = 1 from rfl, Matrix.mul_one, ← Matrix.mul_assoc]
    rw [show Formalism.L2.Theta.mt (GlobalTheory.Doubling.dblSp T) hd * Formalism.L2.Theta.mt (GlobalTheory.Doubling.dblSp T) hd⁻¹ =
      Formalism.L2.Theta.mt (GlobalTheory.Doubling.dblSp T) (hd * hd⁻¹) from rfl, mul_inv_cancel,
      show Formalism.L2.Theta.mt (GlobalTheory.Doubling.dblSp T) 1 = 1 from rfl, Matrix.one_mul]⟩
  have hbox : ∀ p : ι, IsThetaFunO ψ S (GlobalTheory.Doubling.dblSp T) (box p.1.1 p.1.2) := fun p => hθ T _ _ p.2.1 p.2.2
  have hX : ∀ p, IsThetaFunO ψ S (GlobalTheory.Doubling.dblSp T) (X p) := fun p => hωd.om_pres _ _ (hbox p)
  have hY : ∀ p, IsThetaFunO ψ S (GlobalTheory.Doubling.dblSp T) (Y p) := fun p => hθ T _ _ (hω.om_pres _ _ p.2.1) p.2.2
  have hXa : ∀ w p, X (act w p) = heisO ψ S (GlobalTheory.Doubling.dblSp T) (g w) (X p) := fun w p => by
    show ωd (1, hd) (box (heisO ψ S T (top w) p.1.1) (heisO ψ S T (bot w) p.1.2)) = _
    rw [← heisO_box hψ, hωd.om_heis _ _ _ _ (hbox p)]
  have hYa : ∀ w p, Y (act w p) = heisO ψ S (GlobalTheory.Doubling.dblSp T) (g w) (Y p) := fun w p => by
    show box (ω (1, h) (heisO ψ S T (top w) p.1.1)) (heisO ψ S T (bot w) p.1.2) = _
    rw [hω.om_heis _ _ _ _ p.2.1, heisO_box hψ, top_actO hh, bot_actO hh, actO_one_one]
  obtain ⟨μ, 𝓕, μ₁, 𝓕₁, hμ, h𝓕, hμ₁, h𝓕₁, hprod⟩ := GlobalTheory.T.doubledSpace_boxProduct_inner_factorizes D ψ hψ S T
  have hn : ∀ p q : ι, ∫ x in 𝓕, X p x * star (X q x) ∂μ = ∫ x in 𝓕, Y p x * star (Y q x) ∂μ := fun p q => by
    have e1 := GlobalTheory.Mem.LiftPolar.scalar_eq D ψ hψ S (GlobalTheory.Doubling.dblSp T) μ 𝓕 hμ h𝓕 (ωd (1, hd))
      (hωd.om_pres _) (hωd.om_unit μ 𝓕 hμ h𝓕 _) _ _ (hbox p) (hbox q)
    have e2 := GlobalTheory.Mem.LiftPolar.scalar_eq D ψ hψ S T μ₁ 𝓕₁ hμ₁ h𝓕₁ (ω (1, h))
      (hω.om_pres _) (hω.om_unit μ₁ 𝓕₁ hμ₁ h𝓕₁ _) _ _ p.2.1 q.2.1
    show ∫ x in 𝓕, X p x * star (X q x) ∂μ = ∫ x in 𝓕, box (ω (1, h) p.1.1) p.1.2 x * star (box (ω (1, h) q.1.1) q.1.2 x) ∂μ
    rw [e1, hprod _ _ _ _ p.2.1 q.2.1 p.2.2 q.2.2, hprod _ _ _ _ (hω.om_pres _ _ p.2.1) (hω.om_pres _ _ q.2.1) p.2.2 q.2.2, e2]
  obtain ⟨c, hc⟩ := GlobalTheory.T.thetaFun_families_same_heisenberg_inner_eq_smul D ψ hψ S (GlobalTheory.Doubling.dblSp T) ι X Y act g hg hX hY hXa hYa μ 𝓕 hμ h𝓕 hn
  exact ⟨c, fun f₁ f₂ hf₁ hf₂ => hc ⟨(f₁, f₂), hf₁, hf₂⟩⟩

end GlobalTheory.DblThetaRestrict
