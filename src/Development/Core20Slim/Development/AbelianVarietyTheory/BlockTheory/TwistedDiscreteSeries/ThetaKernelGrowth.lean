module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
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
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.PropLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.AddChar
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
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Basic
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.ENNReal.Operations
public import Mathlib.Basic.ENNReal.Real
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.Order.Basic
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField
open GlobalTheory.Grow GlobalTheory.Size
open scoped ENNReal NNReal

namespace GlobalTheory.IndefiniteRowSideFullHecke.ThetaKernelGrowth

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def KernelBound {D : D7} (V W : HSp D) (A d : ℕ) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ →
    ∀ U : AddSubgroup (WO V W), IsOpen (U : Set (WO V W)) →
      ∃ C : ℝ≥0, ∀ (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)),
        IsWeilDatumO ψ V W χS χT ω →
        ∀ (μ : Measure (WO V W)) (𝓕 : Set (WO V W)), IsCovolOne (ratL W V) μ 𝓕 →
          ∀ f ∈ thetaLevel ψ V W U, ∀ (g : GA D V) (h : GA D W),
            ‖thetaKO ω g h f‖ₑ ≤ C * sobO ψ θ μ 𝓕 d f * ENNReal.ofReal ((height V g * height W h) ^ A)

def ThetaGrowth (D : D7) : Prop :=
  ∀ m n : ℕ, ∃ A d : ℕ, ∀ V W : HSp D, V.rank = m → W.rank = n → KernelBound V W A d

def ThetaGrowthUnif : Prop :=
  ∀ r N : ℕ, ∃ A d : ℕ, ∀ (D : D7) (V W : HSp D), Module.finrank ℚ D.host.F = r → V.rank * W.rank = N →
    KernelBound V W A d

theorem ThetaGrowthUnif.thetaGrowth (H : ThetaGrowthUnif) (D : D7) : ThetaGrowth D := fun m n =>
  (H _ (m * n)).imp fun _ h => h.imp fun _ h V W hV hW => h D V W rfl (by rw [hV, hW])

theorem KernelBound.real {D : D7} {V W : HSp D} {A d : ℕ} (H : KernelBound V W A d)
    (ψ : AddChar (AF D.host.F) ℂ) {θ : InfFam D} (hθ : IsInfFam θ) {U : AddSubgroup (WO V W)}
    (hU : IsOpen (U : Set (WO V W))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)),
      IsWeilDatumO ψ V W χS χT ω →
      ∀ (μ : Measure (WO V W)) (𝓕 : Set (WO V W)), IsCovolOne (ratL W V) μ 𝓕 →
        ∀ f ∈ thetaLevel ψ V W U, sobO ψ θ μ 𝓕 d f ≠ ∞ ∧ ∀ (g : GA D V) (h : GA D W),
          ‖ω (g, h) f 0‖ ≤ C * (sobO ψ θ μ 𝓕 d f).toReal * (height V g * height W h) ^ A := by
  obtain ⟨C, hC⟩ := H ψ θ hθ U hU
  refine ⟨C, C.2, fun χS χT ω hω μ 𝓕 hμ f hf => ?_⟩
  have hs := sobO_ne_top hω.std hθ hμ.1 hμ.2.1 hf.1 d
  refine ⟨hs, fun g h => ?_⟩
  have := ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top hs) ENNReal.ofReal_ne_top)
    (hC χS χT ω hω μ 𝓕 hμ f hf g h)
  rwa [toReal_enorm, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.coe_toReal,
    ENNReal.toReal_ofReal (pow_nonneg (mul_pos (height_pos V g) (height_pos W h)).le A)] at this

end GlobalTheory.IndefiniteRowSideFullHecke.ThetaKernelGrowth

end
