module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RaisingLoweringOperators
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColDerApply
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdMinorsMemInv
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Init.ByCases
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.GroupWithZero.Action
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.BigOperators
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ColLie

theorem fockS_eq_colDer_of_same_signs : ∀ {D : D7} {a b : ℕ} (τ : D.what₂.Tau) (ε : Fin a → Bool) (ε' : Fin b → Bool) (Y : Matrix (Fin a) (Fin a) ℂ),
    (∀ i j, ε' i = ε j) →
    GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockS τ ε ε' Y = (GlobalTheory.ColLie.colDer τ Y : Module.End ℂ (PolF D b a)) + (((b : ℂ) / 2) * Y.trace) • 1 := by
  intro D a b τ ε ε' Y h
  have hs : ∀ (i : Fin b) (j k : Fin a), GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.raiO τ ε ε' i j * GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.lowO τ ε ε' i k =
      (LinearMap.mulLeft ℂ (MvPolynomial.X (τ, i, j) : PolF D b a) ∘ₗ
        (MvPolynomial.pderiv (τ, i, k)).toLinearMap : Module.End ℂ (PolF D b a)) := by
    intro i j k
    have hjk : ε j = ε k := (h i j).symm.trans (h i k)
    have h1 : GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.sgn (ε j) * GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.sgn (ε k) = 1 := by
      rw [hjk]; unfold GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.sgn; split_ifs <;> simp
    unfold GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.raiO GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.lowO
    rw [if_pos (h i j), if_pos (h i k), smul_mul_smul_comm, h1, one_smul]
    rfl
  unfold GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockS GlobalTheory.ColLie.colDer
  simp only [hs, Finset.sum_add_distrib, smul_add, Finset.smul_sum]
  congr 1
  · rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin b)))]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_comm]
  · simp only [smul_ite, smul_zero, Finset.sum_const, Finset.card_univ, Fintype.card_fin, Finset.sum_ite_eq,
      Finset.mem_univ, if_true, Matrix.trace, Matrix.diag, Finset.mul_sum, Finset.sum_smul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, smul_smul]
    congr 1
    ring

end GlobalTheory.ColLie
