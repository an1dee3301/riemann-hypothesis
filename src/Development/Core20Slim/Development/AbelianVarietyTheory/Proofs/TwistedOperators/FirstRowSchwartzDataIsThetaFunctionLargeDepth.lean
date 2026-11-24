module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PtYAndItYOfPair
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsThetaFunOOfThetaAt
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsChainPols
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
public import Development.Core20Slim.Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataParams₂
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.Divisibility.LiftLat
public import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.RowTheta

theorem isThetaFunO_cosVec {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil)
    (i : ℕ) (hi : i < D.R.m) (κ : G.CosAt i) :
    IsThetaFunO W.ψ (G.pS (.chi i 0)) (G.pT (.chi i 0)) (W.cosVec i κ) := by
  obtain ⟨e, -, h⟩ := W.cosVec_is
  exact GlobalTheory.VecTheta.isThetaFunO_of_thetaAt W.ψ_std W.θ_is (h i hi κ) (W.vac_is i hi).2.2

theorem isThetaFunO_datum {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil)
    (ρ : G.RealVec) (Φ : G.Datum) (i : Fin D.R.m) :
    IsThetaFunO W.ψ (G.pS (.chi i 0)) (G.pT (.chi i 0)) (W.datum ρ Φ i) :=
  GlobalTheory.Chain.InnerSteps.theta_pureTensorO W.ψ_std W.θ_is _ _ _ _ (isThetaFunO_cosVec W i i.2 (Φ i)) (ρ i)

end GlobalTheory.RowTheta

theorem GlobalTheory.RowTheta.rowDatum_isThetaFunO : GlobalTheory.RowClaim.Big fun {D} _ _ _ _ {_} _ _ _ _ _ {_} ch => ∀ (Φ : ch.G.Datum) (i : Fin D.R.m), IsThetaFunO ch.W.ψ (ch.G.pS (.chi i 0)) (ch.G.pT (.chi i 0)) (ch.W.datum ch.ρ Φ i) :=
  ⟨0, fun _ _ _ => ⟨0, fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ch _ _ Φ i =>
    GlobalTheory.RowTheta.isThetaFunO_datum ch.W ch.ρ Φ i⟩⟩

end
