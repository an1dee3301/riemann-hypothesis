module

public import Mathlib
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.SingToDiffAlt
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Data.Finset.Range
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Logic.Equiv.Defs

@[expose] public section

noncomputable section

open Matrix

namespace PositivityTheory.Rg.Sw.LVs

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def Equivar : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (F : Matrix ι ι ℂ → ℂ) (A : Matrix ι ι ℂ), AnalyticAt ℂ F 0 →
    detD (fun T => F (A * T)) = A.det * detD F

def Reindex : Prop :=
  ∀ (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (e : ι ≃ κ) (F : Matrix κ κ ℂ → ℂ),
    AnalyticAt ℂ F 0 → detD (fun T : Matrix ι ι ℂ => F (T.reindex e e)) = detD F

def KappaFin : Prop :=
  ∀ (N : ℕ) (t : ℤ), detD (fun T : Matrix (Fin N) (Fin N) ℂ => (1 + T).det ^ t) =
    ∏ i ∈ Finset.range N, ((t : ℂ) + i)

end PositivityTheory.Rg.Sw.LVs
