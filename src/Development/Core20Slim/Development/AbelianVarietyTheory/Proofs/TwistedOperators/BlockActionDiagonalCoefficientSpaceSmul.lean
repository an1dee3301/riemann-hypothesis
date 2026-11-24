module

public import Mathlib
public import Formalism.LocalToGlobal.KernelLattices.ThDistC
public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LDrowLemmas
public import Formalism.GradedWeylDivisibility.FinalD
public import Formalism.GradedWeylDivisibility.StatementA
public import Formalism.GradedWeylDivisibility.StatementD
public import Formalism.LocalRingCardinality.DataCoeff
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.PropLemmas
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Nat.Units
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Ker
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.Algebra.Notation.Pi.Basic
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.IsEmpty.Defs
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Basic.Unique
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Order.SetNotation
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

@[expose] public section

open Formalism.L2.Ker MvPolynomial

noncomputable section

namespace GlobalTheory.CoefScale

lemma weight_colW_apply {r n : ℕ} (m : Fin r × Fin n →₀ ℕ) (t : Fin n) :
    Finsupp.weight (Formalism.GradedWeylDivisibility.colW r n) m t = ∑ a : Fin r, m (a, t) := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply,
    Fintype.sum_prod_type_right]
  rw [Finset.sum_eq_single t]
  · refine Finset.sum_congr rfl fun a _ => ?_
    simp [Formalism.GradedWeylDivisibility.colW]
  · intro s _ hs
    refine Finset.sum_eq_zero fun a _ => ?_
    simp [Formalism.GradedWeylDivisibility.colW, Pi.single_apply, Ne.symm hs]
  · simp

theorem rowAct_scalar_dualWeyl {r n : ℕ} (ν : Fin n → ℕ) (c : ℂ) (F : MvPolynomial (Fin r × Fin n) ℂ)
    (hF : F ∈ Formalism.GradedWeylDivisibility.dualWeyl ℂ r n ν) :
    Formalism.GradedWeylDivisibility.rowAct ℂ (Matrix.diagonal fun _ : Fin r => c) F = c ^ (∑ t, ν t) • F := by
  have hw : IsWeightedHomogeneous (Formalism.GradedWeylDivisibility.colW r n) F ν :=
    (mem_weightedHomogeneousSubmodule _ _ _ _).1 (Submodule.mem_inf.1 hF).1
  ext m
  rw [Formalism.GradedWeylDivisibility.ldrow_coeff_rowAct_diag, coeff_smul, smul_eq_mul]
  by_cases h : AddMonoidAlgebra.coeff F m = 0
  · simp [h]
  · have hm := hw h
    rw [Finset.prod_pow_eq_pow_sum, mul_comm]
    congr 2
    simp only [Formalism.GradedWeylDivisibility.rowDeg]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [← weight_colW_apply, hm]

end GlobalTheory.CoefScale

namespace GlobalTheory

theorem blockAct_diag_mem_VV {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → Formalism.BasicNotions.DomWeight n) (c : ι → ℂ)
    (Q : Formalism.L2.DIV.Pol ℂ ι n) (hQ : Q ∈ Formalism.L2.DIV.VV ℂ lam) :
    Formalism.GradedWeylDivisibility.blockAct ℂ (fun τ => Matrix.diagonal fun _ : Fin n => c τ) Q =
      (∏ τ, c τ ^ ∑ a, (lam τ).natW a) • Q := by
  unfold Formalism.L2.DIV.VV Formalism.GradedWeylDivisibility.tensorLat at hQ
  induction hQ using Submodule.span_induction with
  | mem P hP =>
    obtain ⟨F, hF, rfl⟩ := hP
    have h1 := (Formalism.GradedWeylDivisibility.blockActTensor ℂ ℂ ι n n (fun τ => Matrix.diagonal fun _ : Fin n => c τ)).1
    rw [map_prod]
    simp_rw [h1]
    have h2 : ∀ τ, Formalism.GradedWeylDivisibility.rowAct ℂ (Matrix.diagonal fun _ : Fin n => c τ) (F τ) =
        c τ ^ (∑ a, (lam τ).natW a) • F τ := fun τ =>
      GlobalTheory.CoefScale.rowAct_scalar_dualWeyl _ _ _ (hF τ)
    simp_rw [h2, map_smul, Algebra.smul_def, Finset.prod_mul_distrib, map_prod]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add (f := _), hx, hy, smul_add]
  | smul a x _ hx => rw [map_smul, hx, smul_comm]

end GlobalTheory
