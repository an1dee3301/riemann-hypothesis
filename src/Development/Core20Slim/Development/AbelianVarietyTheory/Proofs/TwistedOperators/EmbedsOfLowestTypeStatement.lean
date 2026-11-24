module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.EmbedsOfLowestType
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Batteries.Classes.RatCast
public import Formalism.LocalRingCardinality.DataTheta
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Function
public import Init.Data.Rat.Basic
public import Init.Prelude
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.Defs

@[expose] public section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_injective_intertwiner_of_lowest_type : admQ7 → admQ8 → ∀ (p q : ℕ) (lam : Ix p q → ℚ), IsParam lam → GapGt lam (((p + q : ℕ) : ℝ) ^ 3) → ∀ (A B : UGKMod p q) (u : A.M.V) (v : B.M.V), IsHW A.M.act (blattner lam) u → IsHW B.M.act (blattner lam) v → casimir A.M.act u = (((normSq lam - rhoSq (p + q) : ℚ)) : ℂ) • u → casimir B.M.act v = (((normSq lam - rhoSq (p + q) : ℚ)) : ℂ) • v → IrrGK B.M → ∃ e : B.M.V →ₗ[ℂ] A.M.V, Function.Injective e ∧ e v = u ∧ ∀ Z x, e (B.M.act Z x) = A.M.act Z (e x) := by
  first | exact @GlobalTheory.LowestType.embeds_of_lowest_type | exact GlobalTheory.LowestType.embeds_of_lowest_type | (intros; apply GlobalTheory.LowestType.embeds_of_lowest_type <;> assumption)
