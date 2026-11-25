module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.StepUnfold
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TotalDegreeSubstFLe
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AvgCol

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

def frRel (W : G.Weil) {U : Set T} (N : Std G U) (X : Node) (τ : D.what₂.Tau) :
    Matrix (Fin (G.V X).rank) (Fin (G.V X).rank) ℂ :=
  (W.onb X τ)⁻¹ * N.frC X τ

def frCh (W : G.Weil) {U : Set T} (N : Std G U) (j : ℕ) :
    PolF D (G.V (.top (j + 1))).rank (G.V (.top j)).rank →ₐ[ℂ] PolF D (G.V (.top (j + 1))).rank (G.V (.top j)).rank :=
  GlobalTheory.CompactHowe.substF (fun τ => frRel W N (.top (j + 1)) τ) (fun τ => ((frRel W N (.top j) τ)⁻¹)ᵀ)

def frChInv (W : G.Weil) {U : Set T} (N : Std G U) (j : ℕ) :
    PolF D (G.V (.top (j + 1))).rank (G.V (.top j)).rank →ₐ[ℂ] PolF D (G.V (.top (j + 1))).rank (G.V (.top j)).rank :=
  GlobalTheory.CompactHowe.substF (fun τ => (frRel W N (.top (j + 1)) τ)⁻¹) (fun τ => (frRel W N (.top j) τ)ᵀ)

end GlobalTheory.AvgCol

end
