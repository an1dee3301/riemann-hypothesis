module

public import Development.Core20Slim.Formalism.PieriBlockIdeals.Statement
public import Development.Core20Slim.Formalism.PieriBlockIdeals.StatementLD
public import Development.Core20Slim.Formalism.PieriBlockIdeals.BranchingBoundLastGradedOneRow
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Prelude

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Formalism.CohomologicalDescent.UnitNormBounds

open Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LD
























def UN (N : ℕ) (lam : ℕ → ℕ) (a : ℕ) : ℤ := (lam a : ℤ) + (N : ℤ) - 1 - (a : ℤ)

end Formalism.CohomologicalDescent.UnitNormBounds
