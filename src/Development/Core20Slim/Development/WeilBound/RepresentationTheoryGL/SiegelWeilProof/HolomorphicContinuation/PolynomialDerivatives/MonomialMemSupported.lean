module

public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.AdjoinFirstOperatorsPreservesFamily
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.NullSec
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.CoreSt
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Int.Order
public import Init.Data.Zero
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Submodule.Basic
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Supported
public import Mathlib.Algebra.MvPolynomial.Variables
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Basic.Finite.Prod
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Filter
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Insert
public import Mathlib.Data.Set.Operations
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Order.Nat
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic

@[expose] public section

noncomputable section

open MvPolynomial

namespace PositivityTheory.Rg.Sw.LC.Core

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC

variable {m n : ℕ}

theorem monomial_mem_supported' {S : Set (Fin m × Fin n × Bool)} (s : Fin m × Fin n × Bool →₀ ℕ)
    (hs : ∀ k ∈ s.support, k ∈ S) (a : ℂ) : (monomial s a : PX m n) ∈ supported ℂ S := by
  by_cases ha : a = 0
  · rw [ha, monomial_zero]; exact Subalgebra.zero_mem _
  · rw [mem_supported, vars_monomial ha]
    intro k hk
    exact hs k hk

theorem box_le_first_family (ε : Fin m → Bool) (R : Set (Fin m → ℕ)) : box ε R ≤ F1 (n := n) ε := by
  unfold box
  rw [Submodule.span_le]
  rintro _ ⟨s, hs, -, rfl⟩
  exact monomial_mem_supported' s hs 1

theorem first_family_le_box (ε : Fin m → Bool) : F1 (n := n) ε ≤ box ε Set.univ := by
  intro p hp
  rw [p.as_sum]
  refine Submodule.sum_mem _ fun s hs => ?_
  have hF : ∀ k ∈ s.support, inF1 ε k := by
    intro k hk
    have : k ∈ p.vars := by
      rw [MvPolynomial.mem_vars_iff_mem_support]; exact ⟨s, hs, hk⟩
    exact (mem_supported.mp hp) this
  have : monomial s (p.coeff s) = p.coeff s • (monomial s 1 : PX m n) := by
    rw [smul_monomial, smul_eq_mul, mul_one]
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨s, hF, Set.mem_univ _, rfl⟩)

theorem box_mono (ε : Fin m → Bool) {R R' : Set (Fin m → ℕ)} (h : R ⊆ R') : box (n := n) ε R ≤ box ε R' := by
  unfold box
  refine Submodule.span_mono ?_
  rintro _ ⟨s, hs, hr, rfl⟩
  exact ⟨s, hs, h hr, rfl⟩

theorem box_finiteDimensional (ε : Fin m → Bool) (R : Finset (Fin m → ℕ)) :
    FiniteDimensional ℂ (box (n := n) ε (R : Set (Fin m → ℕ))) := by
  classical
  set M : ℕ := R.sup fun r => ∑ a, r a
  have hfin : {p : PX m n | ∃ s : Fin m × Fin n × Bool →₀ ℕ, (∀ k ∈ s.support, inF1 ε k) ∧ rdeg ε s ∈ (R : Set _) ∧
      p = monomial s 1}.Finite := by
    refine ((Set.finite_univ (α := Fin m × Fin n × Bool → Fin (M + 1))).image
      fun f => (monomial (Finsupp.equivFunOnFinite.symm fun k => (f k : ℕ)) 1 : PX m n)).subset ?_
    rintro _ ⟨s, hs, hr, rfl⟩
    have hle : ∀ k, s k ≤ M := by
      intro k
      by_cases hk : k ∈ s.support
      · have hk1 := hs k hk
        have h1 : s k ≤ rdeg ε s k.1 := by
          unfold rdeg
          have : k = (k.1, k.2.1, !ε k.1) := by
            obtain ⟨a, i, b⟩ := k
            simp only [inF1] at hk1
            simp [hk1]
          rw [this]
          exact Finset.single_le_sum (f := fun i => s (k.1, i, !ε k.1)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)
        have h2 : rdeg ε s k.1 ≤ ∑ a, rdeg ε s a :=
          Finset.single_le_sum (f := fun a => rdeg ε s a) (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)
        have h3 : (∑ a, rdeg ε s a) ≤ M := Finset.le_sup (f := fun r : Fin m → ℕ => ∑ a, r a) (Finset.mem_coe.mp hr)
        omega
      · rw [Finsupp.notMem_support_iff.mp hk]; exact Nat.zero_le _
    refine ⟨fun k => ⟨s k, Nat.lt_succ_of_le (hle k)⟩, Set.mem_univ _, ?_⟩
    congr 1
    ext k
    simp
  exact FiniteDimensional.span_of_finite ℂ hfin

theorem rdeg_filter (ε : Fin m → Bool) (s : Fin m × Fin n × Bool →₀ ℕ) :
    rdeg ε (s.filter (inF1 ε)) = rdeg ε s := by
  funext a
  unfold rdeg
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finsupp.filter_apply_pos]
  simp [inF1]

theorem monomial_split (ε : Fin m → Bool) (s : Fin m × Fin n × Bool →₀ ℕ) (a : ℂ) :
    (monomial s a : PX m n) = monomial (s.filter (inF1 ε)) 1 * monomial (s.filter fun k => ¬ inF1 ε k) a ∧
      (monomial (s.filter (inF1 ε)) 1 : PX m n) ∈ box ε {rdeg ε s} ∧
      (monomial (s.filter fun k => ¬ inF1 ε k) a : PX m n) ∈ F2 ε := by
  refine ⟨by rw [monomial_mul, Finsupp.filter_pos_add_filter_neg, one_mul], ?_, ?_⟩
  · refine Submodule.subset_span ⟨s.filter (inF1 ε), fun k hk => ?_, by simp [rdeg_filter], rfl⟩
    rw [Finsupp.support_filter, Finset.mem_filter] at hk; exact hk.2
  · refine monomial_mem_supported' _ (fun k hk => ?_) a
    rw [Finsupp.support_filter, Finset.mem_filter] at hk
    exact hk.2

end PositivityTheory.Rg.Sw.LC.Core
