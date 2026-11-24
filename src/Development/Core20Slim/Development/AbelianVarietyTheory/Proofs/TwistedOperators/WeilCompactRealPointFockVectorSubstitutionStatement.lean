module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilCompactRealPointFockVectorSubstitution
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqConjOfInFrame
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_compactRealPoint_fockVector_substitution : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (p : Pair T), p.InRange D.R.m →
    ∀ (pS pT : D.what₂.Tau → ℕ), (∀ ρ, pS ρ ≤ (G.pS p).rank) → (∀ ρ, pT ρ ≤ (G.pT p).rank) →
    (∀ ρ, IsCartanInv (gramAt D (G.pS p) ρ) (G.cartS W.cart p ρ)) →
    (∀ ρ, IsCartanInv (gramAt D (G.pT p) ρ) (G.onT W.cart p ρ)) →
    (∀ ρ, IsONBasis (gramAt D (G.pS p) ρ) (G.cartS W.cart p ρ) (G.onS W.onb p ρ) (pS ρ)) →
    (∀ ρ, IsONBasis (gramAt D (G.pT p) ρ) (G.onT W.cart p ρ) (G.onT W.onb p ρ) (pT ρ)) →
    ∀ f : WO (G.pS p) (G.pT p) → ℂ, IsThetaFunO W.ψ _ _ f →
    (∀ ρ, IsFockVacAt (heisO W.ψ _ _) W.θ ρ (cplxO (G.cartS W.cart p ρ) (G.onT W.cart p ρ)) f) →
    ∀ (κS : D.what₂.Tau → Matrix (Fin (G.pS p).rank) (Fin (G.pS p).rank) ℂ)
      (κT : D.what₂.Tau → Matrix (Fin (G.pT p).rank) (Fin (G.pT p).rank) ℂ),
    (∀ ρ, GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.IsKMat (pS ρ) (κS ρ)) → (∀ ρ, GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.IsKMat (pT ρ) (κT ρ)) →
    ∀ (x : GA D (G.pS p)) (y : GA D (G.pT p)), x ∈ GinfC (G.pS p) → y ∈ GinfC (G.pT p) →
    (∀ ρ, compAt W.θ ρ (mt _ x) = G.onS W.onb p ρ * κS ρ * (G.onS W.onb p ρ)⁻¹) →
    (∀ ρ, compAt W.θ ρ (mt _ y) = G.onT W.onb p ρ * κT ρ * (G.onT W.onb p ρ)⁻¹) →
    ∀ c : ℂ, W.om p (x, y) f = c • f → ∀ Q : PolF D (G.pT p).rank (G.pS p).rank,
    W.om p (x, y) (W.fock p f Q) = c • W.fock p f (GlobalTheory.RowReal.fockSubAll pS pT κS κT Q) := by
  first | exact @GlobalTheory.RowReal.om_fock_compact_all | exact GlobalTheory.RowReal.om_fock_compact_all | (intros; apply GlobalTheory.RowReal.om_fock_compact_all <;> assumption)
