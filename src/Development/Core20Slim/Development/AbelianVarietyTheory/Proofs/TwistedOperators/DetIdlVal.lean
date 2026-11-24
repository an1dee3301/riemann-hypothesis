module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairPtsClasses
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairPtsEqSum
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.MovFn
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDetInt
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnramifiedCharacter
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.HeckeThetaElements.IsHeckeElt
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Classical
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.UnitBall
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.RowVertexInv GlobalTheory.SplitFlip
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section

namespace GlobalTheory.RowVacScalar

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}

def idemAt (w : Pl D.host.E) : AE D := Classical.epsilon fun e : AE D => Formalism.L2.NTheta.IsIdemAt e w


open Classical in
def detIdl (e : AE D) (V : HSp D) (g : GA D V) : (AE D)ˣ :=
  if he : e * e = e then GlobalTheory.VecInv.detAt e he V g else 1


open Classical in
theorem detIdl_val {e : AE D} (he : e * e = e) (V : HSp D) (g : GA D V) :
    ((detIdl e V g : (AE D)ˣ) : AE D) = e * (Formalism.L2.Theta.mt V g).det + (1 - e) := by
  rw [detIdl, dite_eq_left he]; rfl

def splitScal (G : GridData L sc) (p : Pair T) (w : Pl D.host.E) (g : GA D (G.pS p)) (h : GA D (G.pT p)) : ℂ :=
  ((splitFacO (G.chrS p) (G.chrT p) (detIdl (idemAt w) (G.pS p) g) (detIdl (idemAt w) (G.pT p) h) : Circle) : ℂ)

end GlobalTheory.RowVacScalar
