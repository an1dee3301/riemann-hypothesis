module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaAtEnlargePlaceIdempotentLatticeIndicator
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.RankCol
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsPlaceModelProdHalf
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isThetaAt_enlarge_placeIdempotent_latticeIndicator : ∀ {D : D7} {S T : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D}
    {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)},
    IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ {f₀ : WO S T → ℂ}, IsVacO ψ θ S T sS sT (ΛS : Set _) (ΛT : Set _) f₀ →
    ∀ {e e' : AE D} {P P' : Finset (Pl D.host.E)}, IsIdemSum e P → IsIdemSum e' P' → P' ⊆ P →
    ∀ {Φ g : WO S T → ℂ}, IsSBHalf e' (latO S T (ΛS : Set _) (ΛT : Set _) fun _ => True) Φ →
    IsThetaAt ψ (symplO S T) (heisO ψ S T) e' (latO S T (ΛS : Set _) (ΛT : Set _) fun _ => True) 1 f₀ Φ g →
    IsSBHalf e (latO S T (ΛS : Set _) (ΛT : Set _) fun _ => True)
        (GlobalTheory.HalfProd.prodHalf e' (e - e') (halfInd (e - e') (latO S T (ΛS : Set _) (ΛT : Set _) fun _ => True)) Φ) ∧
      IsThetaAt ψ (symplO S T) (heisO ψ S T) e (latO S T (ΛS : Set _) (ΛT : Set _) fun _ => True) 1 f₀
        (GlobalTheory.HalfProd.prodHalf e' (e - e') (halfInd (e - e') (latO S T (ΛS : Set _) (ΛT : Set _) fun _ => True)) Φ) g := by
  first | exact @GlobalTheory.ThetaEnlarge.isThetaAt_enlarge | exact GlobalTheory.ThetaEnlarge.isThetaAt_enlarge | (intros; apply GlobalTheory.ThetaEnlarge.isThetaAt_enlarge <;> assumption)
