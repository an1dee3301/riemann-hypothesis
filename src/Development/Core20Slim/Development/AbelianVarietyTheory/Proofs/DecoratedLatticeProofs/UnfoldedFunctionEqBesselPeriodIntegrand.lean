module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.QuasiOfFam
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerBF
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.JacobiToBesselFlatIntertwinesWeilActionStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatSchwartzTargetUnipotentConjBesselCharacterStatement
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ContinuousResTSymm
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompProjAnisotropicAnisotropicEmbedding
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
public import Mathlib.Algebra.Group.Equiv.Defs
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
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf GlobalTheory.Unf.FB

namespace GlobalTheory.Unf.FB.BesselIntegrand

theorem handFB_smul_om {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {σ : ℕ} {J : JacLev D (σ + 1)} {B : BesLev D σ}
    (s : StepFB ψ J B) (vL : VolM D B.L.rank J.W₀.rank) (Y : GA D J.W₀ → WO J.W₀ B.L → ℂ) (Ξ : WO J.W₀ B.V₀ → ℂ)
    (c : ℂ) (h₁ : GA D B.A) :
    handFB s vL Y (c • s.om₀ (1, B.o.emb (h₁, 1)) Ξ) 1 = c * handFB s vL Y Ξ h₁ := by
  unfold handFB
  rw [← integral_const_mul]
  congr 1
  funext h₀
  have e : s.om₀ (h₀, B.o.emb (1, 1)) (c • s.om₀ (1, B.o.emb (h₁, 1)) Ξ) = c • s.om₀ (h₀, B.o.emb (h₁, 1)) Ξ := by
    rw [map_smul, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, ← map_mul, Prod.mk_mul_mk, mul_one, one_mul,
      one_mul]
  unfold pairKer
  rw [e]
  simp only [contractT, thPair, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]
  congr 1
  funext w
  ring

theorem unfF_eq_besFun : ∀ (D : D7), Descent D → ∀ (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (s : StepFB ψ J B), ∀ (vL : VolM D B.L.rank J.W₀.rank) (Y : GA D J.W₀ → WO J.W₀ B.L → ℂ) (G : GA D B.V → ℂ) (Φ : WO J.W B.V → ℂ), IsThetaFunO ψ J.W B.V Φ → ∀ (h : GA D B.V) (h₁ : GA D B.A) (n : flagN B.d), unfF s vL Y G Φ (n.1 * embA B.d B.o h₁ * h) = besFun ψ 1 B.d B.o B.ζ (handFB s vL Y (flatFB s (s.om (1, h) Φ))) (rTrans h G) h₁ n := by
  intro D hD ψ σ J B s vL Y G Φ hΦ h h₁ n
  have h1 : IsThetaFunO ψ J.W B.V (s.om (1, h) Φ) := s.weil.om_pres _ _ hΦ
  have h2 : IsThetaFunO ψ J.W B.V (s.om (1, embA B.d B.o h₁) (s.om (1, h) Φ)) := s.weil.om_pres _ _ h1
  have e : s.om (1, n.1 * embA B.d B.o h₁ * h) Φ = s.om (1, n.1) (s.om (1, embA B.d B.o h₁) (s.om (1, h) Φ)) := by
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, Prod.mk_mul_mk, Prod.mk_mul_mk,
      one_mul, one_mul]
  have c := GlobalTheory.T.jacobiToBesselFlat_intertwines_weilAction D hD ψ σ J B s _ h1 1 h₁
  rw [map_one] at c
  unfold unfF besFun rTrans
  rw [e, GlobalTheory.T.flatSchwartz_targetUnipotent_conj_besselCharacter D hD ψ σ J B s _ h2 n.1 n.2, c, handFB_smul_om]
  ring

end GlobalTheory.Unf.FB.BesselIntegrand
