module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatThetaMapsPreserveThetaFunctionsStatement
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Zero
public import Init.Ext
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic

@[expose] public section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.Unf

theorem om_comp_one {D : D7} {S T : HSp D} (om : Om S T) (g : GA D S) (h : GA D T) (f : WO S T → ℂ) :
    om (1, h) (om (g, 1) f) = om (g, h) f := by
  rw [← Module.End.mul_apply, ← map_mul]
  congr 2
  ext <;> simp

theorem rTrans_liftS {D : D7} {S T : HSp D} (om : Om S T) (ν : Measure (GA D T)) (𝓕 : Set (GA D T))
    (G : GA D T → ℂ) (f : WO S T → ℂ) (g : GA D S) :
    rTrans g (liftS om ν 𝓕 G f) = liftS om ν 𝓕 G (om (g, 1) f) := by
  funext x
  simp only [rTrans, liftS_apply]
  congr 1
  funext h
  have e : ((x, h) : GA D S × GA D T) * (g, 1) = (x * g, h) := by simp
  rw [← e, map_mul, Module.End.mul_apply]

theorem doubleStep_of_laws : ∀ D : D7, UnfBF D → UnfFB D → LinkLaw D → HandFBLaw D → FlatLaw D → DoubleStep D := by
  intro D hBF hFB hLink hHand hFlat ψ σ B J B' s₁ s₂ l vL Φ₁ Φ₂ φ G g hΦ₁ hΦ₂ hφ hG hG'
  have hfl := GlobalTheory.T.flatThetaMaps_preserve_thetaFunctions D hFlat ψ
  have hΞ₁ : ∀ h₁, IsThetaFunO ψ B.V₀ J.W₀ (flatBF s₁ (s₁.om (g, h₁) Φ₁)) := fun h₁ =>
    hfl.1 _ B J s₁ _ (s₁.weil.om_pres _ _ hΦ₁)
  have hΞ₂ : ∀ h₁ h₂, IsThetaFunO ψ J.W₀ B'.V₀ (flatFB s₂ (s₂.om (h₁, h₂) Φ₂)) := fun h₁ h₂ =>
    hfl.2 _ J B' s₂ _ (s₂.weil.om_pres _ _ hΦ₂)
  have hL := fun h₁ => hLink ψ (σ + 1) B J s₁ B'.L B'.ζ B'.line l φ _ hφ (hΞ₁ h₁)
  refine ⟨fun h₁ h₂ => hHand ψ σ J B' s₂ vL _ _ (hL h₁).1 (hΞ₂ h₁ h₂), ?_⟩
  refine ⟨fun h₁ => J.perAll ψ B s₁.om₀ φ (rTrans h₁ (s₂.lift G Φ₂)) (flatBF s₁ (s₁.om (g, h₁) Φ₁)), ?_, ?_⟩
  · have := hBF ψ (σ + 1) B J s₁ φ (s₂.lift G Φ₂) (s₁.om (g, 1) Φ₁) hφ hG' (s₁.weil.om_pres _ _ hΦ₁)
    simp only [om_comp_one] at this
    convert this using 2
    exact rTrans_liftS _ _ _ _ _ _
  · intro h₁
    have := hFB ψ σ J B' s₂ vL _ G (s₂.om (h₁, 1) Φ₂) (hL h₁).1 hG (s₂.weil.om_pres _ _ hΦ₂)
    simp only [om_comp_one] at this
    convert this using 1
    · rfl
    · show J.perAll ψ B s₁.om₀ φ (rTrans h₁ (s₂.lift G Φ₂)) (flatBF s₁ (s₁.om (g, h₁) Φ₁)) = _
      rw [(hL h₁).2]
      congr 1
      exact rTrans_liftS _ _ _ _ _ _

end GlobalTheory.Unf

end
