module

public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.FourierZeroN
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobData
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.NullSec
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Prelude
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

@[expose] public section

noncomputable section

open scoped Matrix
open Formalism.BasicNotions Formalism.BasicNotions.TH

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

def SigAtLeast (D : D7) (V : HSp D) (k : ℕ) : Prop :=
  ∀ τ : D.what₂.Tau, ∃ (ε : Fin V.rank → Bool) (fr : Matrix (Fin V.rank) (Fin V.rank) ℂ),
    IsUnit fr.det ∧ frᴴ * gramAt D V τ * fr = Matrix.diagonal (sgn ε) ∧ k ≤ cnt ε true ∧ k ≤ cnt ε false

def WittLBlt : Prop :=
  ∀ (D : D7) (V : HSp D) (k : ℕ), 2 * k < V.rank → SigAtLeast D V k → k ≤ Formalism.MainNotions.SchurIrreducible.wittIdx V

def WittLBeq : Prop :=
  ∀ (D : D7) (V : HSp D) (k : ℕ), 2 * k = V.rank → SigAtLeast D V k → k ≤ Formalism.MainNotions.SchurIrreducible.wittIdx V

end PositivityTheory.Rg.Sw.Glob
