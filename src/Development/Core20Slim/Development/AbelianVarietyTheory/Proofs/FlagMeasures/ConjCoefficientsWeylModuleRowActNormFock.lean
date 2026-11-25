module

public import Mathlib
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LClosedeqLemmas
public import Formalism.GradedWeylDivisibility.StatementA
public import Formalism.LocalRingCardinality.DataCoeff
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.InterlaceDifferenceShiftInvariant
public import Formalism.RealPlaceAnalysis.FockPairGl
public import Init.Classical
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Zero
public import Init.Prelude
public import Init.PropLemmas
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.MvPolynomial.Monad
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Lattice.Basic
public import Mathlib.Data.Finset.SDiff
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.RingTheory.SimpleRing.Basic

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.Forms Formalism.UG Matrix NumberField IsDedekindDomain
open scoped InnerProductSpace TensorProduct

noncomputable section

namespace GlobalTheory.ConjCoeff

theorem conj_mem_delSq {n : ℕ} (lam : DomWeight n) {p : MvPolynomial (Fin n × Fin n) ℂ}
    (hp : p ∈ delSq ℂ n lam) : MvPolynomial.map (starRingEnd ℂ) p ∈ delSq ℂ n lam := by
  induction hp using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨v, rfl⟩ := hy
    refine Submodule.subset_span ⟨v, ?_⟩
    simp only
    rw [← Formalism.GradedWeylDivisibility.lclosedeq_applyWord_map, Formalism.GradedWeylDivisibility.lclosedeq_hw_map]
  | zero => rw [map_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
  | smul a y _ hy =>
    rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, ← MvPolynomial.smul_eq_C_mul]
    exact Submodule.smul_mem _ _ hy

theorem conj_rowAct {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) (p : MvPolynomial (Fin n × Fin n) ℂ) :
    MvPolynomial.map (starRingEnd ℂ) (Formalism.GradedWeylDivisibility.rowAct ℂ g p) =
      Formalism.GradedWeylDivisibility.rowAct ℂ (g.map (starRingEnd ℂ)) (MvPolynomial.map (starRingEnd ℂ) p) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    have h : ∀ (h : Matrix (Fin n) (Fin n) ℂ) (b : ℂ), Formalism.GradedWeylDivisibility.rowAct ℂ h (MvPolynomial.C b :
        MvPolynomial (Fin n × Fin n) ℂ) = MvPolynomial.C b := fun h b =>
      (Formalism.GradedWeylDivisibility.rowAct ℂ h).commutes b
    rw [h, MvPolynomial.map_C, h]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p v hp =>
    simp only [map_mul, hp, MvPolynomial.map_X]
    congr 1
    simp [Formalism.GradedWeylDivisibility.rowAct]

theorem fockF_conj {σ : Type} (p q : MvPolynomial σ ℂ) :
    Formalism.REAL.fockF (MvPolynomial.map (starRingEnd ℂ) p) (MvPolynomial.map (starRingEnd ℂ) q) =
      Formalism.REAL.fockF q p := by
  classical
  have hs : (MvPolynomial.map (starRingEnd ℂ) p).support = p.support :=
    MvPolynomial.support_map_of_injective _ (starRingEnd ℂ).injective
  unfold Formalism.REAL.fockF
  rw [hs]
  have h1 : ∑ m ∈ p.support, AddMonoidAlgebra.coeff (MvPolynomial.map (starRingEnd ℂ) p) m *
        star (AddMonoidAlgebra.coeff (MvPolynomial.map (starRingEnd ℂ) q) m) *
        ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℂ) =
      ∑ m ∈ p.support ∪ q.support, AddMonoidAlgebra.coeff q m * star (AddMonoidAlgebra.coeff p m) *
        ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℂ) := by
    refine Finset.sum_subset_zero_on_sdiff Finset.subset_union_left ?_ ?_
    · intro m hm
      have : AddMonoidAlgebra.coeff p m = 0 := by
        simpa using (Finset.mem_sdiff.1 hm).2
      simp [this]
    · intro m _
      simp only [MvPolynomial.coeff_map]
      simp [mul_comm]
  have h2 : ∑ m ∈ q.support, AddMonoidAlgebra.coeff q m * star (AddMonoidAlgebra.coeff p m) *
        ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℂ) =
      ∑ m ∈ p.support ∪ q.support, AddMonoidAlgebra.coeff q m * star (AddMonoidAlgebra.coeff p m) *
        ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℂ) := by
    refine Finset.sum_subset_zero_on_sdiff Finset.subset_union_right ?_ (fun _ _ => rfl)
    intro m hm
    have : AddMonoidAlgebra.coeff q m = 0 := by
      simpa using (Finset.mem_sdiff.1 hm).2
    simp [this]
  rw [h1, h2]

theorem conj_coefficients : ∀ (n : ℕ) (lam : DomWeight n), (∀ p ∈ delSq ℂ n lam, MvPolynomial.map (starRingEnd ℂ) p ∈ delSq ℂ n lam) ∧ (∀ (g : Matrix (Fin n) (Fin n) ℂ) (p : MvPolynomial (Fin n × Fin n) ℂ), MvPolynomial.map (starRingEnd ℂ) (Formalism.GradedWeylDivisibility.rowAct ℂ g p) = Formalism.GradedWeylDivisibility.rowAct ℂ (g.map (starRingEnd ℂ)) (MvPolynomial.map (starRingEnd ℂ) p)) ∧ ∀ p q : MvPolynomial (Fin n × Fin n) ℂ, normFock lam (MvPolynomial.map (starRingEnd ℂ) p) (MvPolynomial.map (starRingEnd ℂ) q) = normFock lam q p := by
  intro n lam
  refine ⟨fun p hp => conj_mem_delSq lam hp, conj_rowAct, fun p q => ?_⟩
  rw [normFock, normFock, fockF_conj]

end GlobalTheory.ConjCoeff
