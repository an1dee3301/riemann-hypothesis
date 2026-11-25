module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TraceGlMatrixUnitPowHighestWeightMod
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GoodTopBot
public import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.WeylDualWeylLatticesAgreeOfLowestAlcove
public import Init.Prelude
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Trace

@[expose] public section

open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BasicNotions GlobalTheory.Alc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trace_glMatrixUnit_pow_highestWeight_mod : ∀ (R V : Type) [CommRing R] [AddCommGroup V] [Module R V] (N : ℕ) (E : Matrix (Fin N) (Fin N) (Module.End R V)), GlRel E → ∀ (M : Submodule R V), (∀ a b, ∀ f ∈ M, E a b f ∈ M) → ∀ (μ : Fin N → R) (v : V), (∀ a b, a < b → E a b v ∈ M) → (∀ a, E a a v - μ a • v ∈ M) → ∀ k : ℕ, (E ^ k).trace v - hcVal R μ k • v ∈ M := by
  first | exact @GlobalTheory.Alc.trace_pow_hw | exact GlobalTheory.Alc.trace_pow_hw | (intros; apply GlobalTheory.Alc.trace_pow_hw <;> assumption)
