module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.LatticeFrames.DoubleCollapse
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Localization.FractionRing

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf  GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl

variable {D : D7}

def mono4 {ψ : AddChar (AF D.host.F) ℂ} {σ : ℕ} {B : BesLev D (σ + 1)} {J : JacLev D (σ + 1)} {B' : BesLev D σ}
    (s₁ : StepBF ψ B J) (s₂ : StepFB ψ J B') (a : (AE D)ˣ) (e : Fin 4 → ℤ) : ℂ :=
  chrPow s₁.χV a (e 0) * chrPow s₁.χW a (e 1) * chrPow s₂.χV a (e 2) * chrPow s₂.χW a (e 3)




def HandInv (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (B : BesLev D (σ + 1)) (J : JacLev D (σ + 1)) (B' : BesLev D σ) (s₁ : StepBF ψ B J)
    (s₂ : StepFB ψ J B') (l : Link B B'.L B'.ζ) (vL : VolM D B'.L.rank J.W₀.rank) (Φ₁ : WO B.V J.W → ℂ) (Φ₂ : WO J.W B'.V → ℂ),
    IsThetaFunO ψ B.V J.W Φ₁ → IsThetaFunO ψ J.W B'.V Φ₂ → ∀ φ, IsContAut B.A φ → ∀ g h₁ h₂,
      (∀ r ∈ jacGrp J.d, Chain.hand s₁ s₂ l vL Φ₁ Φ₂ φ g (r * h₁) h₂ = Chain.hand s₁ s₂ l vL Φ₁ Φ₂ φ g h₁ h₂) ∧
      ∀ G, IsContAut B'.V G → ∀ r ∈ besGrp B'.d B'.o,
        B'.per ψ (Chain.hand s₁ s₂ l vL Φ₁ Φ₂ φ g h₁ (r * h₂)) (rTrans (r * h₂) G) =
          B'.per ψ (Chain.hand s₁ s₂ l vL Φ₁ Φ₂ φ g h₁ h₂) (rTrans h₂ G)

end GlobalTheory.FinPl

end
