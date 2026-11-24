module

public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.StatementG
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.EisensteinS2LimitFormula
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Int.DivMod.Basic
public import Init.Prelude
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid

@[expose] public section

noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.D

open Formalism.InvariantFactorPaths.G7 (UnrOK)
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension omegaK)

def normInt (dK : ℕ) (m n : ℤ) : ℤ := m ^ 2 + m * n + n ^ 2 * (((dK : ℤ) + 1) / 4)





end Formalism.L2.Th1.D
