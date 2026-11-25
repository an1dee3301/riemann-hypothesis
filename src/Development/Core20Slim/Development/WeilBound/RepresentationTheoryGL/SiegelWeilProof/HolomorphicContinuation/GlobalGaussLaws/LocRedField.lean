module

public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocalL2IsometryAlt
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaDecompositionUnitary
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelParabolicUnnMatrixBlockUpperTriangular
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.AtTauExUniqueHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SatakeDualWeyl.Statement
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
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Block
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

variable {D : D7} {n : ℕ}

def genSet (D : D7) (n : ℕ) : Set (G D n) :=
  {g | (∃ b, mat g = blk4 1 b 0 1) ∨ (∃ a d, mat g = blk4 a 0 0 d) ∨ (∃ c, mat g = blk4 1 0 c 1)}

def blkDm {R : Type} (M : Matrix (Fin (n + n)) (Fin (n + n)) R) : Matrix (Fin n) (Fin n) R :=
  (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₂

def eI {R : Type} [CommRing R] (I : Finset (Fin n)) : Matrix (Fin n) (Fin n) R :=
  Matrix.diagonal fun i => if i ∈ I then 1 else 0

def wIm {R : Type} [CommRing R] (I : Finset (Fin n)) : Matrix (Fin (n + n)) (Fin (n + n)) R :=
  blk4 (1 - eI I) (eI I) (-eI I) (1 - eI I)

def J2 (R : Type) [CommRing R] (n : ℕ) : Matrix (Fin (n + n)) (Fin (n + n)) R := blk4 0 1 (-1) 0

def UnitD : Prop :=
  ∀ (D : D7) (n : ℕ) (g : G D n), IsUnit (blkDm (mat g)).det → g ∈ Subgroup.closure (genSet D n)

def PIn : Prop := ∀ (D : D7) (n : ℕ), ∀ p ∈ P D n, p ∈ Subgroup.closure (genSet D n)

def LocRedField : Prop :=
  ∀ (k : Type) [Field k] (σ : k →+* k), (∀ a, σ (σ a) = a) → ∀ (n : ℕ) (g : GL (Fin (n + n)) k),
    g ∈ Formalism.UG.UJ σ (J2 k n) → ∃ I : Finset (Fin n), IsUnit (blkDm ((g : Matrix (Fin (n + n)) (Fin (n + n)) k) * wIm I)).det

def LocRedSplit : Prop :=
  ∀ (k : Type) [Field k] (n : ℕ) (g : GL (Fin (n + n)) k), ∃ (a d : GL (Fin n) k) (I : Finset (Fin n)),
    IsUnit (blkDm ((g : Matrix (Fin (n + n)) (Fin (n + n)) k) * blk4 a.1 0 0 d.1 * wIm I)).det

def KInInf : Prop :=
  ∀ (D : D7) (n : ℕ), ∀ k ∈ K D n, (mat k).map (finPart D) = 1 → k ∈ Subgroup.closure (genSet D n)

def KInFin : Prop :=
  ∀ (D : D7) (n : ℕ), ∀ k ∈ K D n, (∀ τ, (mat k).map (Formalism.IndefR.Eqv.psiT D τ) = 1) → k ∈ Subgroup.closure (genSet D n)

end PositivityTheory.Rg.Sw.Glob
