module

public import Mathlib
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.NeZero
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.GroupWithZero.Action
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Module.Submodule.Basic
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Operator.LinearIsometry
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Int.Cast.Lemmas
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Lattice
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Tactic.Ring.RingNF

@[expose] public section

open scoped InnerProductSpace

namespace GlobalTheory

theorem weyl_number_operator_commutation
    (V A κ : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Ring A] [Algebra ℂ A]
    [Fintype κ] (J : V ≃ₗᵢ[ℝ] V) (e : OrthonormalBasis κ ℝ V) (D a c : V → A) (N : A)
    (hJJ : ∀ x, J (J x) = -x) (hadd : ∀ u v, D (u + v) = D u + D v)
    (hsmul : ∀ (r : ℝ) v, D (r • v) = (r : ℂ) • D v)
    (hcomm : ∀ u v, D u * D v - D v * D u =
      (2 * Real.pi * Complex.I * (inner ℝ u (J v) : ℝ) : ℂ) • 1)
    (hc : ∀ z, c z = D z - Complex.I • D (J z)) (ha : ∀ z, a z = -(D z + Complex.I • D (J z)))
    (hN : N = ∑ j, c (e j) * a (e j)) :
    (∀ z, a z * c z - c z * a z = ((4 * Real.pi * ‖z‖ ^ 2 : ℝ) : ℂ) • 1) ∧
    (∀ z, N * c z = c z * (N + ((8 * Real.pi : ℝ) : ℂ) • 1)) ∧
    (∀ z, N * a z = a z * (N - ((8 * Real.pi : ℝ) : ℂ) • 1)) ∧
    ∀ z, D z ∈ Submodule.span ℂ (Set.range (fun j => a (e j)) ∪ Set.range fun j => c (e j)) := by
  have I3 : Complex.I ^ 3 = -Complex.I := by rw [pow_succ, Complex.I_sq]; ring
  have hJl : ∀ u v, inner ℝ (J u) v = -inner ℝ u (J v) := by
    intro u v
    have h := J.inner_map_map (J u) v
    rw [hJJ, inner_neg_left] at h
    linarith
  have hJself : ∀ z, inner ℝ z (J z) = 0 := by
    intro z
    have h := hJl z z
    have h' := real_inner_comm z (J z)
    linarith
  have hDneg : ∀ w, D (-w) = -D w := by
    intro w
    have h := hsmul (-1) w
    simpa using h
  have key : ∀ F : V → A, (∀ u v, F (u + v) = F u + F v) →
      (∀ (r : ℝ) v, F (r • v) = (r : ℂ) • F v) →
      ∀ w, F w = ∑ j, ((inner ℝ (e j) w : ℝ) : ℂ) • F (e j) := by
    intro F hFa hFs w
    have h := map_sum (AddMonoidHom.mk' F hFa) (fun j => inner ℝ (e j) w • e j) Finset.univ
    simp only [AddMonoidHom.mk'_apply, e.sum_repr'] at h
    rw [h]
    exact Finset.sum_congr rfl fun j _ => hFs _ _
  have hca : ∀ u v, c (u + v) = c u + c v := by
    intro u v; rw [hc, hc, hc, map_add (f := _), hadd, hadd, smul_add]; abel
  have hcs : ∀ (r : ℝ) v, c (r • v) = (r : ℂ) • c v := by
    intro r v; rw [hc, hc, map_smul, hsmul, hsmul, smul_sub, smul_comm Complex.I (r : ℂ)]
  have haa' : ∀ u v, a (u + v) = a u + a v := by
    intro u v; rw [ha, ha, ha, map_add (f := _), hadd, hadd, smul_add]; abel
  have has : ∀ (r : ℝ) v, a (r • v) = (r : ℂ) • a v := by
    intro r v
    rw [ha, ha, map_smul, hsmul, hsmul, smul_comm Complex.I (r : ℂ), ← smul_add, smul_neg]
  have hcJ : ∀ w, c (J w) = Complex.I • c w := by
    intro w
    rw [hc, hc, hJJ, hDneg]
    simp only [smul_sub, smul_neg, smul_smul, Complex.I_mul_I, neg_one_smul]
    abel
  have haJ : ∀ w, a (J w) = -(Complex.I • a w) := by
    intro w
    rw [ha, ha, hJJ, hDneg]
    simp only [smul_add, smul_neg, smul_smul, Complex.I_mul_I, neg_one_smul, neg_neg]
    abel
  have hsw : ∀ u v, D u * D v = D v * D u +
      (2 * Real.pi * Complex.I * (inner ℝ u (J v) : ℝ) : ℂ) • 1 := by
    intro u v; rw [← hcomm u v]; abel
  have hac : ∀ z w, a z * c w - c w * a z =
      (4 * (Real.pi : ℂ) * ((inner ℝ z w : ℝ) : ℂ)
        - 4 * Real.pi * Complex.I * ((inner ℝ z (J w) : ℝ) : ℂ)) • (1 : A) := by
    intro z w
    rw [ha, hc]
    simp only [mul_sub, sub_mul, mul_add, add_mul, neg_mul, mul_neg, smul_mul_assoc, mul_smul_comm]
    rw [hsw z w, hsw z (J w), hsw (J z) w, hsw (J z) (J w)]
    simp only [hJJ, map_neg, inner_neg_right, inner_neg_left, hJl, neg_neg]
    match_scalars <;> (ring_nf; try simp only [Complex.I_sq, I3]; try ring_nf)
  have hcc : ∀ z w, c z * c w = c w * c z := by
    intro z w
    rw [← sub_eq_zero, hc, hc]
    simp only [mul_sub, sub_mul, mul_add, add_mul, neg_mul, mul_neg, smul_mul_assoc, mul_smul_comm]
    rw [hsw z w, hsw z (J w), hsw (J z) w, hsw (J z) (J w)]
    simp only [hJJ, map_neg, inner_neg_right, inner_neg_left, hJl, neg_neg]
    match_scalars <;> (ring_nf; try simp only [Complex.I_sq, I3]; try ring_nf)
  have haa : ∀ z w, a z * a w = a w * a z := by
    intro z w
    rw [← sub_eq_zero, ha, ha]
    simp only [mul_sub, sub_mul, mul_add, add_mul, neg_mul, mul_neg, smul_mul_assoc, mul_smul_comm]
    rw [hsw z w, hsw z (J w), hsw (J z) w, hsw (J z) (J w)]
    simp only [hJJ, map_neg, inner_neg_right, inner_neg_left, hJl, neg_neg]
    match_scalars <;> (ring_nf; try simp only [Complex.I_sq, I3]; try ring_nf)
  have hcsum := key c hca hcs
  have hasum := key a haa' has
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro z
    rw [hac, hJself, real_inner_self_eq_norm_sq]
    congr 1
    push_cast
    ring
  · intro z
    have hterm : ∀ j, c (e j) * a (e j) * c z - c z * (c (e j) * a (e j)) =
        (4 * (Real.pi : ℂ)) • (((inner ℝ (e j) z : ℝ) : ℂ) • c (e j))
          - (4 * Real.pi * Complex.I) • (((inner ℝ (e j) (J z) : ℝ) : ℂ) • c (e j)) := by
      intro j
      rw [mul_assoc, ← mul_assoc (c z), hcc z (e j), mul_assoc, ← mul_sub, hac (e j) z,
        mul_smul_comm, mul_one]
      module
    have hsum : N * c z - c z * N = ((8 * Real.pi : ℝ) : ℂ) • c z := by
      rw [hN, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
      simp only [hterm, Finset.sum_sub_distrib, ← Finset.smul_sum]
      rw [← hcsum z, ← hcsum (J z), hcJ, smul_smul, ← sub_smul]
      congr 1
      push_cast
      ring_nf
      simp only [Complex.I_sq]
      ring
    rw [mul_add, mul_smul_comm, mul_one, ← sub_eq_iff_eq_add', hsum]
  · intro z
    have hterm : ∀ j, c (e j) * a (e j) * a z - a z * (c (e j) * a (e j)) =
        -((4 * (Real.pi : ℂ)) • (((inner ℝ (e j) z : ℝ) : ℂ) • a (e j))
          + (4 * Real.pi * Complex.I) • (((inner ℝ (e j) (J z) : ℝ) : ℂ) • a (e j))) := by
      intro j
      have h1 := hac z (e j)
      have h2 : inner ℝ z (J (e j)) = -inner ℝ (e j) (J z) := by
        rw [real_inner_comm (J (e j)) z, hJl]
      rw [real_inner_comm (e j) z, h2] at h1
      have h3 : c (e j) * a (e j) * a z - a z * (c (e j) * a (e j)) =
          -((a z * c (e j) - c (e j) * a z) * a (e j)) := by
        rw [mul_assoc, haa (e j) z]
        noncomm_ring
      rw [h3, h1, smul_mul_assoc, one_mul]
      simp only [Complex.ofReal_neg]
      module
    have hsum : N * a z - a z * N = -(((8 * Real.pi : ℝ) : ℂ) • a z) := by
      rw [hN, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
      simp only [hterm, Finset.sum_neg_distrib, Finset.sum_add_distrib, ← Finset.smul_sum]
      rw [← hasum z, ← hasum (J z), haJ, smul_neg, smul_smul, ← sub_eq_add_neg, ← sub_smul]
      congr 2
      push_cast
      ring_nf
      simp only [Complex.I_sq]
      ring
    rw [mul_sub, mul_smul_comm, mul_one, sub_eq_iff_eq_add.mp hsum]
    abel
  · intro z
    have hDz : D z = (1 / 2 : ℂ) • (c z - a z) := by
      rw [hc, ha]
      module
    rw [hDz, hcsum z, hasum z]
    refine Submodule.smul_mem _ _ (Submodule.sub_mem _ ?_ ?_) <;>
      refine Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    · exact Or.inr ⟨j, rfl⟩
    · exact Or.inl ⟨j, rfl⟩

end GlobalTheory
