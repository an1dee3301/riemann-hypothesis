module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOscillatorActionUnitaryPolynomialBound
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsQuadOfPlane
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOscillatorActionUnitaryGroupHermitian
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergSmoothOfWeakDerivativeClosedSet
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.PolarConjTranspose
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.CommuteGelfandInvariantMatrixUnitsOfGlRel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousFourierGau
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.MetricSpace.Algebra
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Cauchy
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open MeasureTheory Complex Matrix GlobalTheory.RealWeil GlobalTheory.Mem.Lift
open scoped RealInnerProductSpace ContDiff Real ComplexOrder Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasDerivAt_oscillatorAction_unitaryPath_quadratic : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℂ), Hᴴ = H → H.det ≠ 0 → ∀ (B : Type) [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B] (ρ : (ι → ℂ) → B →L[ℂ] B), IsHeis (fun x y => (star y ⬝ᵥ H *ᵥ x).im) ρ → ∀ (G : Type) [Group G] (m : G →* Matrix ι ι ℂ), (∀ g, (m g)ᴴ * H * m g = H) → ∃ Ω : G → B → B, IsOsc ρ (fun g v => m g *ᵥ v) Ω ∧ (∃ N : ℕ, ∀ f, Sm ρ f → ∃ C : ℝ, ∀ g, ‖Ω g f‖ ≤ C * (1 + ∑ i, ∑ j, ‖m g i j‖) ^ N) ∧ ∀ (γ : ℝ → G) (X : Matrix ι ι ℂ), γ 0 = 1 → (∀ i j, HasDerivAt (fun t => m (γ t) i j) (X i j) 0) → ∀ (κ : Type) [Fintype κ] (c : κ → ℂ) (p q : κ → ι → ℂ), IsQuadOf (fun x y => (star y ⬝ᵥ H *ᵥ x).im) (fun v => X *ᵥ v) c p q → ∃ lam : ℂ, ∀ f, Sm ρ f → HasDerivAt (fun t => Ω (γ t) f) (quad ρ c p q f + lam • f) 0 := by
  first | exact @GlobalTheory.Mem.Lift.OscBound.exists_osc_bound_deriv | exact GlobalTheory.Mem.Lift.OscBound.exists_osc_bound_deriv | (intros; apply GlobalTheory.Mem.Lift.OscBound.exists_osc_bound_deriv <;> assumption)
