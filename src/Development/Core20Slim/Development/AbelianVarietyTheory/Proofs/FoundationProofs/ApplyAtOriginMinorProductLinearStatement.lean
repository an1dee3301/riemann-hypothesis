module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FoundationProofs.ApplyAtOriginMinorProductLinear
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.PairingDivisors.StatementH
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
public import Init.Classical
public import Init.Data.Nat.Lemmas
public import Init.Prelude
public import Init.PropLemmas
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Sets
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Fin.Basic
public import Mathlib.Order.Monotone.Defs
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.applyAtOrigin_minorProduct_linear : ∀ (D : D7) (a d : ℕ) (n : D.what₂.Tau → ℕ) (G : VC D a d → ℂ), Differentiable ℂ G → (∀ (u : D.what₂.Tau → Matrix (Fin a) (Fin a) ℂ) (t : Tup D a d n), GL3Theta.applyAt0 D (minorPol D t) (fun z => G (fun τ => (Matrix.of (z τ) * u τ : Matrix _ _ ℂ))) = (∏ τ, (u τ).det ^ n τ) * GL3Theta.applyAt0 D (minorPol D t) G) ∧ (∀ (u : D.what₂.Tau → Matrix (Fin d) (Fin d) ℂ), (∀ τ, u τ ∈ Matrix.unitaryGroup (Fin d) ℂ) → ∑ t : Tup D a d n, ‖GL3Theta.applyAt0 D (minorPol D t) (fun z => G (fun τ => (u τ * Matrix.of (z τ) : Matrix _ _ ℂ)))‖ ^ 2 = ∑ t : Tup D a d n, ‖GL3Theta.applyAt0 D (minorPol D t) G‖ ^ 2) ∧ (∀ (c : ℂ) P, GL3Theta.applyAt0 D P (c • G) = c * GL3Theta.applyAt0 D P G) ∧ ∀ G' P, Differentiable ℂ G' → GL3Theta.applyAt0 D P (G + G') = GL3Theta.applyAt0 D P G + GL3Theta.applyAt0 D P G' := by
  first | exact @GlobalTheory.NormSum.applyAt0_minorPol_linear | exact GlobalTheory.NormSum.applyAt0_minorPol_linear | (intros; apply GlobalTheory.NormSum.applyAt0_minorPol_linear <;> assumption)
