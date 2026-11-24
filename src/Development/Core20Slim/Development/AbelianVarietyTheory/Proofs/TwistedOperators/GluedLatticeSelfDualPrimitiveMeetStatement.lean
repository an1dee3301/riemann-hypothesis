module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.GluedLatticeSelfDualPrimitiveMeet
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatGlueLatIffDual
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FlatSpaceComponents
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatIffOfSelfDual
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Lattice.Full
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.NumberTheory.NumberField.Basic

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Matrix
open Formalism.L2.DIV (Pl)
open Formalism.IndefR.Lev (EAf)
open Formalism.IndefR.Datum (IsSelfDualC)
open GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents GlobalTheory.AdIsom
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gluedLattice_selfDual_primitive_meet : ∀ (D : D7) (u : D.what₂.Word) (Y X : HSp D) (ι : X.V →ₗ[D.host.E] Y.V) (z : Y.V), IsLine Y X ι z u → ∀ (L₀ : Lat X) (x₀ : X.V), Submodule.IsFullLattice D.host.E L₀ → IsGlueVec X u L₀ (vA X x₀) → IsSDIn Y (flatSp Y X ι z) (glueLat Y X ι z u L₀ x₀) ∧ IsPrim Y z (glueLat Y X ι z u L₀ x₀) ∧ capX Y X ι (glueLat Y X ι z u L₀ x₀) = L₀ := by
  first
  | exact @GlobalTheory.GlueVecLattice.glueLat_selfDual_prim_cap
  | intro D u Y X ι z h L₀ x₀ hL hg
    exact GlobalTheory.GlueVecLattice.glueLat_selfDual_prim_cap D u Y X ι z h L₀ x₀ hL.toIsLattice hg
