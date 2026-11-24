module

public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.ConvRight
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.NullSec
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Basis
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.RingTheory.Derivation.Basic

@[expose] public section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open MvPolynomial

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

variable {D : D7} {m n : ℕ}

def IsUe (ε : Fin m → Bool) (X : Matrix (Fin m) (Fin m) ℂ) : Prop :=
  Xᴴ * Matrix.diagonal (sgn ε) + Matrix.diagonal (sgn ε) * X = 0

def xyP (X : Matrix (Fin m) (Fin m) ℂ) (a : Fin m) (i : Fin n) (b : Bool) : PX m n :=
  ∑ c, C (if b then star (X a c) else X a c) * MvPolynomial.X (c, i, b)

def vfX (c : ℝ) (X : Matrix (Fin m) (Fin m) ℂ) (P : PX m n) : PX m n :=
  ∑ a, ∑ i, (xyP X a i false * pderiv (a, i, false) P + xyP X a i true * pderiv (a, i, true) P -
    C (c : ℂ) * (xyP X a i false * MvPolynomial.X (a, i, true) + xyP X a i true * MvPolynomial.X (a, i, false)) * P)

def zRe (ε : Fin m → Bool) (a b : Fin m) : Matrix (Fin m) (Fin m) ℂ :=
  (1 / 2 : ℂ) • (Matrix.single a b 1 - (sgn ε a * sgn ε b) • Matrix.single b a 1)

def zIm (ε : Fin m → Bool) (a b : Fin m) : Matrix (Fin m) (Fin m) ℂ :=
  (-(Complex.I / 2) : ℂ) • (Matrix.single a b 1 + (sgn ε a * sgn ε b) • Matrix.single b a 1)


end PositivityTheory.Rg.Sw.Glob
