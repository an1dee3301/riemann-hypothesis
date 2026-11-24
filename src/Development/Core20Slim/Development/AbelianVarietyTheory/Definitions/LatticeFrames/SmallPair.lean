module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.LatticeFrames.VacOfShape
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValueDoubleUnif
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CombAtSingleZero
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ContinuousResTSymm
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompProjAnisotropicAnisotropicEmbedding
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Prelude
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
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl

variable {D : D7}



def Reps {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type}
    {p : ι → SplitPt D k} {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (ψ : AddChar (AF D.host.F) ℂ)
    {S T : HSp D} (α : ∀ i, Frame (p i) S n') (β : ∀ i, Frame (p i) T n) (LS : Lat S) (LT : Lat T)
    (Ψ : ι → Matrix n n' k → ℂ) (I : List ι) (P : Pl D → Prop) (c : WO S T →₀ ℂ) : Prop :=
  CombAt P c ∧ ∀ f, Vac ψ S T LS LT P f → OverAll ψ α β LS LT Ψ I f (comb ψ S T c f)














def FlatVac (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (P : Pl D → Prop),
    (∀ (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (s : StepBF ψ B J) (LV : Lat B.V) (LV₀ : Lat B.V₀) (LW : Lat J.W)
      (LW₀ : Lat J.W₀), (∀ x, P x → GoodBF ψ B J LV LV₀ LW LW₀ x) → ∀ Φ, Vac ψ B.V J.W LV LW P Φ →
      Vac ψ B.V₀ J.W₀ LV₀ LW₀ P (flatBF s Φ)) ∧
    (∀ (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (s : StepFB ψ J B) (LV : Lat J.W) (LV₀ : Lat J.W₀) (LW : Lat B.V)
      (LW₀ : Lat B.V₀), (∀ x, P x → AdaptFB ψ J B LV LV₀ LW LW₀ x) → ∀ Φ, Vac ψ J.W B.V LV LW P Φ →
      Vac ψ J.W₀ B.V₀ LV₀ LW₀ P (flatFB s Φ)) ∧
    ∀ (V V₀ T : HSp D) (d : HypDec V V₀ 0) (L : Lat V) (L₀ : Lat V₀) (LT : Lat T), IsSelfDualC V L → IsSelfDualC V₀ L₀ →
      IsSelfDualC T LT → (∀ x, P x → MonoAt d L L₀ x) → ∀ Φ, Vac ψ V T L LT P Φ → Vac ψ V₀ T L₀ LT P fun w => Φ (d.ext0 T w)

def LastVac (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V₀ A L S X T L'' : HSp D) (o : OrthDec V₀ A L) (o'' : OrthDec X T L'')
    (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E), L.rank = 1 → L''.rank = 1 →
    τᴴ * (L.gram * τ) = (-(D.host.xi0 * star D.host.xi0)) • L''.gram →
    ∀ (P : Pl D → Prop) (M : Lat V₀) (LA : Lat A) (LS : Lat S) (LX : Lat X) (LT : Lat T), IsSelfDualC V₀ M → IsSelfDualC A LA →
      IsSelfDualC S LS → IsSelfDualC X LX → IsSelfDualC T LT →
      (∀ x, P x → Tame D x ∧ ∃ (LL : Lat L) (LZ : Lat L''), IsSelfDualC L LL ∧ IsSelfDualC L'' LZ ∧ OrthAt o M LA LL x ∧
        OrthAt o'' LX LT LZ x ∧ ∀ w ∈ latO S L'' (LS : Set _) (LZ : Set _) (· = x),
          kap τ S w ∈ latO L S (LL : Set _) (LS : Set _) (· = x)) →
      ∀ Ξ Φ₂, Vac ψ V₀ S M LS P Ξ → Vac ψ S T LS LT P Φ₂ → BiVacAt ψ LA LS LX P (lastBi o o'' τ Ξ Φ₂)

end GlobalTheory.FinPl

end
