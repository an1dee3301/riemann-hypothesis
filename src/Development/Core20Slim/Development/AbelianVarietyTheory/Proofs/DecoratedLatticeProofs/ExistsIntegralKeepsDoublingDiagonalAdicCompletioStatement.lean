module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIntegralKeepsDoublingDiagonalAdicCompletio
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
public import Development.Core20Slim.Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TrivialParameterBound
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
public import Development.AbelianVarietyTheory.Definitions.Foundations.MemSiegelOfIffRightAct
public import Formalism.SatakeDualWeyl.StatementE
public import Formalism.SatakeDualWeyl.StatementF
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.PRep
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke ordL)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (bcParam)
open GlobalTheory.LFun (toCompl locMat locChar IsSplitChart IsInertChart IsFrameAt KGL IsSatVecGL IsSatVecU eulerFac UnrAt LvTw dv Fam)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_keepsDoublingDiagonal_adicCompletion : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (ϖ : w.adicCompletion E), IsUnifV E w ϖ → ∀ (d : Fin n → ℤ) (t k₁ k₂ : GL (Fin n) (w.adicCompletion E)), t.1 = Matrix.diagonal (fun i => ϖ ^ d i) → k₁ ∈ KGL w (n := n) → k₂ ∈ KGL w (n := n) → ∃ κ ∈ KGL w (n := (n + n)), KeepsDiag finSumFinEquiv (blkGL finSumFinEquiv (k₁ * t * k₂, 1) * κ).1 ∧ ordL (leviMat finSumFinEquiv (blkGL finSumFinEquiv (k₁ * t * k₂, 1) * κ).1).det = ∑ i, max (d i) 0 ∧ ordL (quotMat finSumFinEquiv (blkGL finSumFinEquiv (k₁ * t * k₂, 1) * κ).1).det = ∑ i, min (d i) 0 := by
  first | exact @GlobalTheory.GraphShear.graph_shear | exact GlobalTheory.GraphShear.graph_shear | (intros; apply GlobalTheory.GraphShear.graph_shear <;> assumption)
