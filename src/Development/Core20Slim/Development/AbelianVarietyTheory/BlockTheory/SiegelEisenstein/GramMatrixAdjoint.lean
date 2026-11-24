module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ModerateGrowthSchwartz
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
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
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Bounds.Defs
public import Mathlib.Order.Lattice.Nat
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Trace.Defs

@[expose] public section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField
open scoped TensorProduct NNReal Matrix ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def blocks {R : Type} {n : ℕ} (a b c d : Matrix (Fin n) (Fin n) R) : Matrix (Fin (n + n)) (Fin (n + n)) R :=
  (Matrix.fromBlocks a b c d).submatrix finSumFinEquiv.symm finSumFinEquiv.symm

variable (D : D7)

def skewJ (n : ℕ) : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E := blocks 0 1 (-1) 0

abbrev UA {k : ℕ} (T : Matrix (Fin k) (Fin k) D.host.E) : Type := AdelicU.GAd D.sp.cm.sig T

abbrev GG (n : ℕ) : Type := UA D (skewJ D n)

variable {D}

def mat {k : ℕ} {T : Matrix (Fin k) (Fin k) D.host.E} (g : UA D T) : Matrix (Fin k) (Fin k) (AE D) :=
  (AdelicU.matHom (AF D.host.F) D.sp.cm.sig T g).1

def mmul {k l r : ℕ} (x : Mx D k l) (y : Mx D l r) : Mx D k r := HMul.hMul x y

def adj {k l : ℕ} (x : Mx D k l) : Mx D l k := Formalism.UG.cT (cA D) x

variable (D)

variable {D}

section Space

variable {m n : ℕ} (T : Matrix (Fin m) (Fin m) D.host.E)

def wittIdx : ℕ :=
  sSup {r | ∃ W : Submodule D.host.E (Fin m → D.host.E),
    (∀ x ∈ W, ∀ y ∈ W, hE D.sp.cm.sig T x y = 0) ∧ Module.finrank D.host.E W = r}

def gramQ (x y : Mx D m n) : Mx D n n :=
  mmul (mmul (adj x) (T.map (incA D))) y

def trA (z : AE D) : AF D.host.F := Algebra.trace (AF D.host.F) (AE D) z

def quadTr (b : Mx D n n) (x : Mx D m n) : AF D.host.F :=
  algebraMap D.host.F (AF D.host.F) (1 / 2) * trA (Matrix.trace (mmul b (gramQ T x x)))

def pairing (ψ : AddChar (AF D.host.F) ℂ) (x y : Mx D m n) : ℂ := ψ (trA (Matrix.trace (gramQ T x y)))

end Space

abbrev Sch (θ : InfFam D) (m n : ℕ) : Type := ModerateGrowthSchwartz.schwartzA θ m n

abbrev Rep (θ : InfFam D) (n : ℕ) {m : ℕ} (T : Matrix (Fin m) (Fin m) D.host.E) : Type :=
  GG D n × UA D T →* Module.End ℂ (Sch θ m n)

section Weil

variable {θ : InfFam D} {m n : ℕ} {T : Matrix (Fin m) (Fin m) D.host.E}



def s0 (m n : ℕ) : ℂ := (m : ℂ) / 2 - (n : ℂ) / 2

def sect (α : GG D n → ℝ≥0) (ω : Rep θ n T) (Φ : Sch θ m n) (s : ℂ) (g : GG D n) : ℂ :=
  ((α g : ℝ) : ℂ) ^ (s - s0 m n) * (ω (g, 1) Φ).1 0

end Weil

end GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks

end
