module

public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocRedField
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.AtTauExUniqueHolds
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

noncomputable section

open scoped Matrix TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open GlobalTheory.AdelicU GlobalTheory.StdUnn IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

variable {D : D7} {n : ℕ}

abbrev Ev (D : D7) (v : GlobalTheory.FinPl.Pl D) := Fv D.host.F v ⊗[D.host.F] D.host.E

def IsIntUnit {D : D7} {v : GlobalTheory.FinPl.Pl D} (z : Ev D v) : Prop :=
  z ∈ intLoc D.host.F D.host.E v ∧ ∃ z' ∈ intLoc D.host.F D.host.E v, z * z' = 1

def cTv {D : D7} {v : GlobalTheory.FinPl.Pl D} (a : Matrix (Fin n) (Fin n) (Ev D v)) : Matrix (Fin n) (Fin n) (Ev D v) :=
  (a.map (sigR (Fv D.host.F v) D.sp.cm.sig)).transpose

def LocGood {D : D7} {v : GlobalTheory.FinPl.Pl D} (kv : Matrix (Fin (n + n)) (Fin (n + n)) (Ev D v))
    (a : Matrix (Fin n) (Fin n) (Ev D v)) (I : Finset (Fin n)) : Prop :=
  (∀ i j, a i j ∈ intLoc D.host.F D.host.E v) ∧ IsIntUnit a.det ∧
    IsIntUnit (blkDm (kv * blk4 a 0 0 (cTv a)⁻¹ * wIm I)).det

def LocFin : Prop :=
  ∀ (D : D7) (n : ℕ), ∀ k ∈ K D n, ∀ v : GlobalTheory.FinPl.Pl D,
    ∃ (a : Matrix (Fin n) (Fin n) (Ev D v)) (I : Finset (Fin n)), LocGood ((mat k).map (GlobalTheory.FinPl.compAt D v)) a I

def GlueLevi : Prop :=
  ∀ (D : D7) (n : ℕ) (a : ∀ v : GlobalTheory.FinPl.Pl D, Matrix (Fin n) (Fin n) (Ev D v)),
    (∀ v i j, a v i j ∈ intLoc D.host.F D.host.E v) → (∀ v, IsIntUnit (a v).det) →
    ∃ m : G D n, m ∈ genSet D n ∧ (∀ v, (mat m).map (GlobalTheory.FinPl.compAt D v) = blk4 (a v) 0 0 (cTv (a v))⁻¹) ∧
      ∀ τ, (mat m).map (Formalism.IndefR.Eqv.psiT D τ) = 1

def GlueW : Prop :=
  ∀ (D : D7) (n : ℕ) (I : GlobalTheory.FinPl.Pl D → Finset (Fin n)),
    ∃ w ∈ Subgroup.closure (genSet D n), (∀ v, (mat w).map (GlobalTheory.FinPl.compAt D v) = wIm (I v)) ∧
      ∀ τ, (mat w).map (Formalism.IndefR.Eqv.psiT D τ) = 1

def UnitAE : Prop :=
  ∀ (D : D7) (d : AE D), (∀ τ, Formalism.IndefR.Eqv.psiT D τ d ≠ 0) → (∀ v, IsIntUnit (GlobalTheory.FinPl.compAt D v d)) → IsUnit d

end PositivityTheory.Rg.Sw.Glob
