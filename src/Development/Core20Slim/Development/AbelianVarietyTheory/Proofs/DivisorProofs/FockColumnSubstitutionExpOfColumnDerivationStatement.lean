module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockColumnSubstitutionExpOfColumnDerivation
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColDerApply
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdMinorsMemInv
public import Init.Data.Cast
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
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
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
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
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Algebra
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockColumnSubstitution_exp_of_columnDerivation : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (d a : ℕ) (τ : ι) (c : ℕ) (Q : Type) [AddCommGroup Q] [Module ℂ Q]
    (q : GlobalTheory.MinorFrame.Pol ι d a →ₗ[ℂ] Q),
    (∀ (S : Matrix (Fin a) (Fin a) ℂ) (R : GlobalTheory.MinorFrame.Pol ι d a) (m : GlobalTheory.MinorFrame.Var ι d a →₀ ℕ),
      HasDerivAt (fun h : ℝ => AddMonoidAlgebra.coeff (GlobalTheory.MinorFrame.colSub (GlobalTheory.ColLie.atPl τ (NormedSpace.exp ((h : ℂ) • S))) R) m)
        (AddMonoidAlgebra.coeff (GlobalTheory.ColLie.colDer τ S R) m) 0) →
    (∀ S : Matrix (Fin a) (Fin a) ℂ, S.conjTranspose = -S → ∀ P, q (GlobalTheory.ColLie.colDer τ S P) = ((c : ℂ) * S.trace) • q P) →
    ∀ S : Matrix (Fin a) (Fin a) ℂ, S.conjTranspose = -S → ∀ P,
      q (GlobalTheory.MinorFrame.colSub (GlobalTheory.ColLie.atPl τ (NormedSpace.exp S)) P) = ((NormedSpace.exp S).det ^ c) • q P := by
  first | exact @GlobalTheory.ColLie.colSub_exp_of_colDer | exact GlobalTheory.ColLie.colSub_exp_of_colDer | (intros; apply GlobalTheory.ColLie.colSub_exp_of_colDer <;> assumption)
