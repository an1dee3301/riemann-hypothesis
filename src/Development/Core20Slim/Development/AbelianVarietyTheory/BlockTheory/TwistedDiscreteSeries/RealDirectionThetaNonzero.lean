module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.List.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
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
public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Trace.Defs
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.IndefiniteRowSideFullHecke.RealDirectionThetaNonzero

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def l2Sq {S T : HSp D} (μ : Measure (WO S T)) (𝓕 : Set (WO S T)) (f : WO S T → ℂ) : ℝ≥0∞ :=
  ∫⁻ w in 𝓕, ‖f w‖ₑ ^ 2 ∂μ

def l2InnerPairing {S T : HSp D} (μ : Measure (WO S T)) (𝓕 : Set (WO S T)) (f f' : WO S T → ℂ) : ℂ :=
  ∫ w in 𝓕, f w * starRingEnd ℂ (f' w) ∂μ

def IsRealDir {S T : HSp D} (L : ℝ →+ WO S T) : Prop :=
  Continuous L ∧ ∀ t, (L t).map (finPart D) = 0

def dHeis (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (L : ℝ →+ WO S T) (f : WO S T → ℂ) : WO S T → ℂ :=
  fun x => deriv (fun t : ℝ => heisO ψ S T (L t) f x) 0

def dHeisWord (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (Ls : List (ℝ →+ WO S T)) (f : WO S T → ℂ) :
    WO S T → ℂ :=
  Ls.foldr (dHeis ψ S T) f

def HasLevel (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (U : AddSubgroup (WO S T)) (f : WO S T → ℂ) : Prop :=
  ∀ u ∈ U, u.map (infPart D) = 0 → heisO ψ S T u f = f

def IsThetaCont (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (ℓ : (WO S T → ℂ) →ₗ[ℂ] ℂ) : Prop :=
  ∀ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) →
    ∃ (words : List (List (ℝ →+ WO S T))) (C : ℝ), (∀ Ls ∈ words, ∀ L ∈ Ls, IsRealDir L) ∧
      ∀ f, IsThetaFunO ψ S T f → HasLevel ψ S T U f →
        ∀ B : ℝ, 0 ≤ B → (∀ Ls ∈ words, ∀ w, ‖dHeisWord ψ S T Ls f w‖ ≤ B) → ‖ℓ f‖ ≤ C * B

def Schur (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) : Prop :=
  ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL T S) 𝓕 μ →
    ∀ A : Module.End ℂ (WO S T → ℂ),
      (∀ f, IsThetaFunO ψ S T f → IsThetaFunO ψ S T (A f)) →
      (∀ w f, IsThetaFunO ψ S T f → A (heisO ψ S T w f) = heisO ψ S T w (A f)) →
      (∃ C : ℝ≥0, ∀ f, IsThetaFunO ψ S T f → l2Sq μ 𝓕 (A f) ≤ (C : ℝ≥0∞) * l2Sq μ 𝓕 f) →
      ∃ c : ℂ, ∀ f, IsThetaFunO ψ S T f → A f = c • f

def ThetaUnique (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) : Prop :=
  ∀ ℓ : (WO S T → ℂ) →ₗ[ℂ] ℂ,
    (∀ γ f, IsThetaFunO ψ S T f → ℓ (heisO ψ S T (ratW T S γ) f) = ℓ f) →
    IsThetaCont ψ S T ℓ →
    ∃ c : ℂ, ∀ f, IsThetaFunO ψ S T f → ℓ f = c * f 0

def CovolOneExists (S T : HSp D) : Prop :=
  ∃ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕

def HeisenbergLemma (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) : Prop :=
  ∀ (μ μ' : Measure (WO S T)) (𝓕 𝓕' : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → IsCovolOne (ratL T S) μ' 𝓕' →
    ∀ f f', IsThetaFunO ψ S T f → IsThetaFunO ψ S T f' →
      IntegrableOn (fun ξ => heisO ψ S T ξ f 0 * starRingEnd ℂ (heisO ψ S T ξ f' 0)) 𝓕 μ ∧
      IntegrableOn (fun w => f w * starRingEnd ℂ (f' w)) 𝓕' μ' ∧
      ∫ ξ in 𝓕, heisO ψ S T ξ f 0 * starRingEnd ℂ (heisO ψ S T ξ f' 0) ∂μ = l2InnerPairing μ' 𝓕' f f'

def ThetaNonzero (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) : Prop :=
  ∃ f, IsThetaFunO ψ S T f ∧ f ≠ 0

def ThetaFactsAt (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) : Prop :=
  Schur ψ S T ∧ ThetaUnique ψ S T ∧ (CovolOneExists S T ∧ HeisenbergLemma ψ S T) ∧ ThetaNonzero ψ S T

def ThetaFacts (D : D7) : Prop :=
  ∀ ψ : AddChar (AF D.host.F) ℂ, IsCharAF D.host.F ψ → ∀ S T : HSp D, ThetaFactsAt ψ S T

theorem ThetaFacts.std (h : ThetaFacts D) {ψ : AddChar (AF D.host.F) ℂ} {s : ℤ} (hψ : IsStdChar D ψ s) (S T : HSp D) :
    ThetaFactsAt ψ S T := h ψ hψ.1 S T

theorem symplOH_zero_left (S T : HSp D) (y : WO S T) : symplOH S T 0 y = 0 := by
  simp [symplOH, symplO, hO]

theorem heisO_apply_zero (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (ξ : WO S T) (f : WO S T → ℂ) :
    heisO ψ S T ξ f 0 = f ξ := by
  simp [heisO, symplOH_zero_left]

end GlobalTheory.IndefiniteRowSideFullHecke.RealDirectionThetaNonzero

end
