module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsGLSubmatrix
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsDatOfTower
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ContinuousResTSymm
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsOrthDec
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.TopOrthEmb
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Module.Submodule.Map
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Defs
public import Mathlib.Order.Defs.Lattice
public import Mathlib.RingTheory.FractionalIdeal.Basic
public import Mathlib.RingTheory.FractionalIdeal.Inverse
public import Mathlib.RingTheory.FractionalIdeal.Operations
public import Mathlib.RingTheory.Localization.FractionRing

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal

noncomputable section

open scoped nonZeroDivisors

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowShape

variable {D : D7}

def latPi (S : HSp D) (I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) : GlobalTheory.FinPl.Lat S :=
  Submodule.pi Set.univ fun _ => (I : Submodule (𝓞 D.host.E) D.host.E)


variable (D) in
def tiltSc (j : ℕ) (p : Fin (D.R.m - 1 - j)) : D.host.E :=
  if Odd j then
    (if 2 * p.1 < D.R.m - 1 - j then (D.host.xi0 ^ p.1)⁻¹ else star (D.host.xi0 ^ (D.R.m - 1 - j - 1 - p.1)))
  else 1


variable (D) in
def rowId (j : ℕ) (p : Fin (D.R.m - 1 - j)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E :=
  FractionalIdeal.spanSingleton _ (tiltSc D j p) * stairId D.host.AA D.host.AAbar (D.R.m - 1 - j) p

variable {T : Type} {L : LevCh D T} {sc : Consts}

def rowN (G : GridData L sc) (j : ℕ) : GlobalTheory.FinPl.Lat (G.V (.grid D.R.m j)) :=
  if h : j < D.R.m then (G.rowDec j h).lat (G.Λ (.top j)) (rowId D j) else G.Λ (.grid D.R.m j)


variable (D) in
def lineId (j : ℕ) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E :=
  D.host.AA ^ ((D.R.m - 2 - j) / 2 + 1) * (D.host.AAbar ^ ((D.R.m - 2 - j) / 2 + 1))⁻¹


variable (D) in
def lineL (j : ℕ) : GlobalTheory.FinPl.Lat (GlobalTheory.SeeSaw.Model.nLine D) := latPi _ (lineId D j)


variable (D) in
def topL : GlobalTheory.FinPl.Lat (GlobalTheory.RowChain.pLine D) := latPi _ 1

def coreL (G : GridData L sc) (j : ℕ) : GlobalTheory.FinPl.Lat (GlobalTheory.Doubling.hsum (G.V (.top j)) (GlobalTheory.SeeSaw.Model.nLine D)) :=
  (G.Λ (.top j)).map
      ((Matrix.mulVecLin (GlobalTheory.OrthSumExists.orthDecHsum D (G.V (.top j)) (GlobalTheory.SeeSaw.Model.nLine D)).iA).restrictScalars
        (𝓞 D.host.E)) ⊔
    (lineL D j).map
      ((Matrix.mulVecLin (GlobalTheory.OrthSumExists.orthDecHsum D (G.V (.top j)) (GlobalTheory.SeeSaw.Model.nLine D)).iB).restrictScalars
        (𝓞 D.host.E))

end GlobalTheory.RowShape

end
