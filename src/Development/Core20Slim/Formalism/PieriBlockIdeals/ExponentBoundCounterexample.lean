module

public import Mathlib
public import Development.Core20Slim.Formalism.PieriBlockIdeals.Statement
public import Development.Core20Slim.Formalism.RankGapBounds.CloudMinFalse
public import Development.Core20Slim.Formalism.PieriBlockIdeals.StatementLA

@[expose] public section

open MvPolynomial CategoryTheory TensorProduct

noncomputable section

namespace Formalism.CohomologicalDescent.SL2BinomialLattices

open Formalism.GradedWeylDivisibility Formalism.RankGapBounds.JumpSetsAlt Formalism.CohomologicalDescent.LA

universe u v u' v'


structure Shape (N k h S eta : ℕ) (xm lo : ℤ) (U : Fin N → ℤ) : Prop where
  anti : StrictAnti U
  inRange : ∀ a, 0 ≤ U a ∧ U a ≤ (h : ℤ)
  k_le : k ≤ N
  cloudIn : ∀ a : Fin N, a.val < k → xm ≤ U a ∧ U a ≤ xm + (S : ℤ)
  restIn : ∀ a : Fin N, k ≤ a.val → lo ≤ U a ∧ U a ≤ lo + (eta : ℤ)








end Formalism.CohomologicalDescent.SL2BinomialLattices
