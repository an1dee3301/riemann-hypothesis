module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasDerivAtInnerPolynomialMovingGaussian
public import Formalism.LocalRingCardinality.DataTheta
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.OscActMonomialOfUnique
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsNegBaseY
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.Analysis.CStarAlgebra.Module.Defs
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Sum
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.Topology.MetricSpace.Algebra
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH GlobalTheory.Mem.Osc GlobalTheory.OscGauss Matrix
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasDerivAt_inner_polynomial_moving_gaussian : ∀ (P Q : ℕ) (F : Fock (Ix P Q)) (A : ℝ → Matrix (Fin P) (Fin Q) ℂ) (x : ℝ → Ix P Q → ℂ) (v : ℝ → F.H) (A' : Matrix (Fin P) (Fin Q) ℂ) (x' : Ix P Q → ℂ), (∀ t, HasCoeff F (v t) (expPS (gaussPoly (A t) (x t)))) → (∀ i j, HasDerivAt (fun t => A t i j) (A' i j) 0) → (∀ l, HasDerivAt (fun t => x t l) (x' l) 0) → ∀ f : MvPolynomial (Ix P Q) ℂ, HasDerivAt (fun t => inner ℂ (F.ι f) (v t)) (∑ i, ∑ j, A' i j * inner ℂ (F.ι (MvPolynomial.pderiv (Sum.inl i) (MvPolynomial.pderiv (Sum.inr j) f))) (v 0) + ∑ l, x' l * inner ℂ (F.ι (MvPolynomial.pderiv l f)) (v 0)) 0 := by
  first | exact @GlobalTheory.OscPairDer.hasDerivAt_inner_gauss | exact GlobalTheory.OscPairDer.hasDerivAt_inner_gauss | (intros; apply GlobalTheory.OscPairDer.hasDerivAt_inner_gauss <;> assumption)
