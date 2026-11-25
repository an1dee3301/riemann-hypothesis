module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.SandwichedFlipRouteThroughSmallEqInvConstRouteBi
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.PathArgsOfNotMem
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Definitions.Divisors.BplusOfEquivariant
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Finsupp.Single
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped Pointwise

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sandwichedFlip_routeThroughSmall_eq_inv_const_routeBig : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} (M : Vol G) (B : Frames G) (ρ : RealMatch W) (t : T) (i j : ℕ) (hi : i < D.R.m) (hj : j < D.R.m) (c : ℂ), c ≠ 0 → CommutesWith W B ρ t ⟨i, hi⟩ ⟨j, hj⟩ c → M.Is t → GlobalTheory.FlipRun.CuspStep W M ρ t → ∀ (A : Path T (.grid 0 D.R.m) (.grid i (j + 1))) (Bp : Path T (.grid (i + 1) j) (.grid D.R.m 0)), GlobalTheory.FlipRun.OnGrid D.R.m t A → GlobalTheory.FlipRun.OnGrid D.R.m t Bp → ∀ (e : AE D), IsIdemSum e (locPl G t) → ∀ (α : PureT G A) (β : PureT G Bp) (φA : PureT G A) (φB : PureT G Bp), GlobalTheory.FlipRun.VecAll ρ e A φA α → GlobalTheory.FlipRun.VecAll ρ e Bp φB β → ∀ (σs : TotT G (routeSmall t i j)) (σb : TotT G (routeBig t i j)) (Φ : ∀ w, Matrix (Fin ((locGrid G t w).rank (i, j))) ((locGrid G t w).Cols i j) (Kw w) → ℂ), (∀ w ∈ locPl G t, GlobalTheory.SplitFlip.IsNatDatum (unifAt w) (depthAt G w) (Φ w)) → HasFlip B t ρ ⟨i, hi⟩ ⟨j, hj⟩ (depthAt G) Φ σb σs → ∀ F : Fn G (.grid 0 D.R.m), GlobalTheory.FlipRun.IsCuspListed W.θ _ F → ∀ Q : GlobalTheory.FlipRun.PolE G →₀ ℂ, liftT W M _ (GlobalTheory.FlipRun.tensE W _ Q (((σs).sum fun d c => Finsupp.single (((α).append d).append (β)) c) : TotT G ((A.comp (routeSmall t i j)).comp Bp))) F = c⁻¹ • liftT W M _ (GlobalTheory.FlipRun.tensE W _ (GlobalTheory.FlipRun.flipPolE ρ i j Q) (((σb).sum fun d c => Finsupp.single (((α).append d).append (β)) c) : TotT G ((A.comp (routeBig t i j)).comp Bp))) F := by
  first | exact @GlobalTheory.FlipRun.oneFlip_sandwich | exact GlobalTheory.FlipRun.oneFlip_sandwich | (intros; apply GlobalTheory.FlipRun.oneFlip_sandwich <;> assumption)
