module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowShiftTheta
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Definitions.Divisors.InvVolConjLevelOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.LastVertexInv

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.LastVertexMove

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

def colPt (S : GridChoice W U) (t : T) (g : FinPt G (.top D.R.m)) :
    GA D (G.pS (.top t (lastIx D))) × GA D (G.pT (.top t (lastIx D))) :=
  G.toPair (.top t (lastIx D)) 1 (topLast ((S.N.u (.top D.R.m))⁻¹ * g * S.N.u (.top D.R.m))).1

theorem colShift_eq (S : GridChoice W U) (t : T) (g : FinPt G (.top D.R.m)) :
    colShift S t g = W.om _ (colPt S t g) := rfl

def rowPt (S : GridChoice W U) (k : FinPt G (.grid D.R.m D.R.m)) :
    GA D (G.pS (.chi (lastIx D) D.R.m : Pair T)) × GA D (G.pT (.chi (lastIx D) D.R.m : Pair T)) :=
  G.toPair (.chi (lastIx D) D.R.m) 1 (gridLast ((S.N.u (.grid D.R.m D.R.m))⁻¹ * k * S.N.u (.grid D.R.m D.R.m))).1

theorem rowShift_eq (S : GridChoice W U) (k : FinPt G (.grid D.R.m D.R.m)) :
    rowShift S k = W.om (.chi (lastIx D) D.R.m) (rowPt S k) := rfl

def stdLat (S : GridChoice W U) (p : Pair T) : AddSubgroup (WO (G.pS p) (G.pT p)) :=
  latO (G.pS p) (G.pT p) (S.N.latS p : Set _) (S.N.latT p : Set _) fun _ => True

end GlobalTheory.LastVertexMove

namespace GlobalTheory.LastVertexMove

variable {D : D7}

def moveFn {A B : HSp D} (q : GA D A × GA D B) (Φ : WO A B → ℂ) : WO A B → ℂ := fun x => Φ (actO A B q.1⁻¹ q.2⁻¹ x)

end GlobalTheory.LastVertexMove
