module

public import Mathlib
public import Development.Core20Slim.Formalism.PeriodIntegrals.GTDefs
public import Formalism.LocalRingCardinality.DataCoeff
public import Development.Core20Slim.Formalism.PeriodIntegrals.GTBranch
public import Init.Prelude

@[expose] public section

noncomputable section

namespace PI

open Formalism.BasicNotions MvPolynomial

def GTLower : Prop :=
  ∀ (n N : ℕ) (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n), Interlace h lam sg → Branch h lam sg

end PI
