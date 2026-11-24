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
















def harm (l h : ℕ) (i : ℝ) : ℝ :=
  if h < l then 0 else (i / (l : ℝ)) * (1 + Real.log ((h : ℝ) / (l : ℝ)))

def labelSumBoundPos (l k t h : ℕ) (i : ℝ) (xm xp mB : ℤ) : ℝ :=
  (k : ℝ) * (((xp - xm : ℤ) : ℝ) / (l : ℝ) + IlInd l xm xp mB) +
    (if ((d0 l (xm - mB) : ℕ) : ℤ) < xm - mB then
      min (min (k : ℝ) (t : ℝ)) (i / (d0 l (xm - mB) : ℝ)) else 0) +
    harm l h i





def cPrime (l k j t q h ecl : ℕ) (xm xp mB : ℤ) (I : ℝ) : ℝ :=
  ((q : ℝ) + 2 * (j : ℝ)) * (((h : ℝ) - 1) / ((l : ℝ) - 1)) + (ecl : ℝ) + labelSumBoundPos l k t h I xm xp mB

def cCoarse (l k j t q h N' ecl : ℕ) (xm xp mB : ℤ) (I : ℝ) : ℝ :=
  ((q : ℝ) + 2 * (j : ℝ)) * (((h : ℝ) + (N' : ℝ)) / ((l : ℝ) - 1) + 6) + (ecl : ℝ) +
    (k : ℝ) * (((xp - xm : ℤ) : ℝ) / (l : ℝ) + IlInd l xm xp mB) +
    (if ((d0 l (xm - mB) : ℕ) : ℤ) < xm - mB then
      min (min (k : ℝ) (t : ℝ)) (I / (d0 l (xm - mB) : ℝ)) else 0) +
    (I / (l : ℝ)) * (1 + Real.posLog ((h : ℝ) / (l : ℝ)))

def UN (N : ℕ) (lam : ℕ → ℕ) (a : ℕ) : ℤ := (lam a : ℤ) + (N : ℤ) - 1 - (a : ℤ)

end Formalism.CohomologicalDescent.UnitNormBounds
