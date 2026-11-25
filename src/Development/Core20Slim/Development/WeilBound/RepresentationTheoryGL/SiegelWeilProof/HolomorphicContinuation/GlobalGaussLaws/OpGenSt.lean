module

public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocalL2IsometryAlt
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocOpSt
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.NullSec
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.CStarMatrix
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Logic.Equiv.Defs

@[expose] public section

noncomputable section

open scoped Matrix

namespace PositivityTheory.Rg.Sw.Glob

def SchOps : Prop :=
  ∀ (m n : ℕ), (∀ f g : (Fin m → Fin n → ℂ) → ℂ, IsSch f → IsSch g → IsSch (fun u => f u + g u)) ∧
    (∀ (c : ℂ) (f : (Fin m → Fin n → ℂ) → ℂ), IsSch f → IsSch (fun u => c * f u)) ∧
    (∀ (a : Matrix (Fin n) (Fin n) ℂ) (f : (Fin m → Fin n → ℂ) → ℂ), IsUnit a.det → IsSch f →
      IsSch (fun u => f (Matrix.of u * a))) ∧
    (∀ (ε : Fin m → Bool) (t : ℝ) (b : Matrix (Fin n) (Fin n) ℂ) (f : (Fin m → Fin n → ℂ) → ℂ), bᴴ = b → IsSch f →
      IsSch (fun u => Complex.exp (Complex.I * (t : ℂ) * (b * gramX ε u).trace) * f u)) ∧
    ∃ f : (Fin m → Fin n → ℂ) → ℂ, IsSch f ∧ f 0 = 1

end PositivityTheory.Rg.Sw.Glob
