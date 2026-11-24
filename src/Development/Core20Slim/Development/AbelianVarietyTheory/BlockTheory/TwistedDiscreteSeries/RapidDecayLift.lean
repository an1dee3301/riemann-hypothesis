module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsGrowthSobNeTopOfIsAutFunSm
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DifferentiableOneP
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedSmooth
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.PropLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
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
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.CompleteBooleanAlgebra
public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Algebra
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.Grow GlobalTheory.Size GlobalTheory.Mem.AutSpace
open scoped ENNReal NNReal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IndefiniteRowSideFullHecke.RapidDecayLift

variable {D : D7}

section Defs

variable (θ : InfFam D) {V W : HSp D} (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ))
  (ν : Measure (GA D W)) (𝓕 : Set (GA D W))

def lift (f : WO V W → ℂ) (F : GA D W → ℂ) : GA D V → ℂ := Lift.liftInt ν 𝓕 (thetaKO ω) f F

def dOmS (τ : D.what₂.Tau) (X : Matrix (Fin V.rank) (Fin V.rank) ℂ) (f : WO V W → ℂ) : WO V W → ℂ :=
  fun z => deriv (fun t : ℝ => ω (oneP θ V τ X t, 1) f z) 0

def dOmT (τ : D.what₂.Tau) (Y : Matrix (Fin W.rank) (Fin W.rank) ℂ) (f : WO V W → ℂ) : WO V W → ℂ :=
  fun z => deriv (fun t : ℝ => ω (1, oneP θ W τ Y t) f z) 0

def decayInt (A : ℕ) (F : GA D W → ℂ) : ℝ≥0∞ := ∫⁻ h in 𝓕, ENNReal.ofReal (‖F h‖ * quotHeight W h ^ A) ∂ν

end Defs

structure LiftLaws (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ) {V W : HSp D}
    (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ν : Measure (GA D W)) (𝓕 : Set (GA D W))
    (cls : (GA D W → ℂ) → Prop) : Prop where

  integ : ∀ f F, IsThetaFunO ψ V W f → cls F → ∀ g h₀,
    IntegrableOn (fun h => thetaKO ω g h f * rTr W h₀ F h) 𝓕 ν

  integ_der : ∀ f F, IsThetaFunO ψ V W f → cls F → ∀ τ, ∀ Y ∈ lieAt W τ, ∀ g,
    IntegrableOn (fun h => thetaKO ω g h f * Rder θ W τ Y F h) 𝓕 ν

  aut : ∀ f F, IsThetaFunO ψ V W f → cls F → IsAutFun V (lift ω ν 𝓕 f F)

  equiv : ∀ f F, IsThetaFunO ψ V W f → cls F → ∀ g₀ h₀,
    lift ω ν 𝓕 (ω (g₀, h₀) f) (rTr W h₀ F) = rTr V g₀ (lift ω ν 𝓕 f F)

  smooth : ∀ f F, IsThetaFunO ψ V W f → cls F → lift ω ν 𝓕 f F ∈ SmFun θ V

  dS : ∀ f, IsThetaFunO ψ V W f → ∀ τ, ∀ X ∈ lieAt V τ, IsThetaFunO ψ V W (dOmS θ ω τ X f) ∧
    ∀ z, HasDerivAt (fun t : ℝ => ω (oneP θ V τ X t, 1) f z) (dOmS θ ω τ X f z) 0

  dT : ∀ f, IsThetaFunO ψ V W f → ∀ τ, ∀ Y ∈ lieAt W τ, IsThetaFunO ψ V W (dOmT θ ω τ Y f) ∧
    ∀ z, HasDerivAt (fun t : ℝ => ω (1, oneP θ W τ Y t) f z) (dOmT θ ω τ Y f z) 0

  derS : ∀ f F, IsThetaFunO ψ V W f → cls F → ∀ τ, ∀ X ∈ lieAt V τ,
    Rder θ V τ X (lift ω ν 𝓕 f F) = lift ω ν 𝓕 (dOmS θ ω τ X f) F

  derT : ∀ f F, IsThetaFunO ψ V W f → cls F → ∀ τ, ∀ Y ∈ lieAt W τ, ∀ g,
    HasDerivAt (fun s : ℝ => lift ω ν 𝓕 (ω (1, oneP θ W τ Y s) f) (rTr W (oneP θ W τ Y s) F) g)
      (lift ω ν 𝓕 f (Rder θ W τ Y F) g + lift ω ν 𝓕 (dOmT θ ω τ Y f) F g) 0

  growth : ∀ f F, IsThetaFunO ψ V W f → cls F → UnifModGrowth V θ (lift ω ν 𝓕 f F)

  decay_ne_top : ∀ F, cls F → ∀ A, decayInt ν 𝓕 A F ≠ ∞

  bound : ∃ A : ℕ, ∀ k : ℕ, ∃ d : ℕ, ∀ (μ : Measure (WO V W)) (𝓓 : Set (WO V W)), μ.IsAddHaarMeasure →
    IsAddFundamentalDomain (ratL W V) 𝓓 μ → ∀ U : AddSubgroup (WO V W), IsOpen (U : Set (WO V W)) →
      ∃ C : ℝ≥0, ∀ f ∈ thetaLevel ψ V W U, ∀ F, cls F →
        growthSob θ V k A (lift ω ν 𝓕 f F) ≤ C * sobO ψ θ μ 𝓓 d f * decayInt ν 𝓕 A F

def LiftPropsOn (D : D7) (cls : InfFam D → (W : HSp D) → (GA D W → ℂ) → Prop) : Prop :=
  ∀ (V W : HSp D) (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle)
    (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsInfFam θ → IsWeilDatumO ψ V W χS χT ω →
    ∀ (ν : Measure (GA D W)) (𝓕 : Set (GA D W)), ν.IsHaarMeasure → IsFundamentalDomain (GQ W) 𝓕 ν →
      LiftLaws θ ψ ω ν 𝓕 (cls θ W)

def LiftProps (D : D7) : Prop := LiftPropsOn D fun θ W F => IsAutFunSm θ W F ∧ IsCuspFun W F

def LiftPropsRapid (D : D7) : Prop := LiftPropsOn D fun θ W F => RapidDecSm θ W F

theorem LiftLaws.mono {θ : InfFam D} {ψ : AddChar (AF D.host.F) ℂ} {V W : HSp D}
    {ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} {ν : Measure (GA D W)} {𝓕 : Set (GA D W)}
    {cls cls' : (GA D W → ℂ) → Prop} (h : LiftLaws θ ψ ω ν 𝓕 cls) (hc : ∀ F, cls' F → cls F) :
    LiftLaws θ ψ ω ν 𝓕 cls' := by
  refine
    { integ := fun f F hf hF => h.integ f F hf (hc F hF)
      integ_der := fun f F hf hF => h.integ_der f F hf (hc F hF)
      aut := fun f F hf hF => h.aut f F hf (hc F hF)
      equiv := fun f F hf hF => h.equiv f F hf (hc F hF)
      smooth := fun f F hf hF => h.smooth f F hf (hc F hF)
      dS := h.dS
      dT := h.dT
      derS := fun f F hf hF => h.derS f F hf (hc F hF)
      derT := fun f F hf hF => h.derT f F hf (hc F hF)
      growth := fun f F hf hF => h.growth f F hf (hc F hF)
      decay_ne_top := fun F hF => h.decay_ne_top F (hc F hF)
      bound := ?_ }
  obtain ⟨A, hA⟩ := h.bound
  refine ⟨A, fun k => (hA k).imp fun d hd μ 𝓓 h1 h2 U hU => ?_⟩
  exact (hd μ 𝓓 h1 h2 U hU).imp fun C hC f hf F hF => hC f hf F (hc F hF)

theorem liftProps_of_rapid (hP : GlobalTheory.Published.CuspRapidDecay) (h : LiftPropsRapid D) : LiftProps D :=
  fun V W θ ψ χS χT ω hθ hω ν 𝓕 hν h𝓕 => (h V W θ ψ χS χT ω hθ hω ν 𝓕 hν h𝓕).mono fun _ hF =>
    rapidDecSm_of_cuspForm hP hθ hF.1 hF.2

theorem decayInt_le {W : HSp D} (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (A : ℕ) (F : GA D W → ℂ) :
    decayInt ν 𝓕 A F ≤ decaySize W A F * ν 𝓕 := by
  rw [← setLIntegral_const]
  exact lintegral_mono fun h => le_iSup (fun g => ENNReal.ofReal (‖F g‖ * quotHeight W g ^ A)) h

theorem LiftLaws.derT_add {θ : InfFam D} {ψ : AddChar (AF D.host.F) ℂ} {V W : HSp D}
    {ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} {ν : Measure (GA D W)} {𝓕 : Set (GA D W)}
    {cls : (GA D W → ℂ) → Prop} (h : LiftLaws θ ψ ω ν 𝓕 cls) {f : WO V W → ℂ} {F : GA D W → ℂ}
    (hf : IsThetaFunO ψ V W f) (hF : cls F) (τ : D.what₂.Tau) {Y : Matrix (Fin W.rank) (Fin W.rank) ℂ}
    (hY : Y ∈ lieAt W τ) (g : GA D V) :
    lift ω ν 𝓕 f (Rder θ W τ Y F) g + lift ω ν 𝓕 (dOmT θ ω τ Y f) F g = 0 := by
  have := h.derT f F hf hF τ Y hY g
  simp only [h.equiv f F hf hF] at this
  exact this.unique (hasDerivAt_const _ _)

end GlobalTheory.IndefiniteRowSideFullHecke.RapidDecayLift

end
