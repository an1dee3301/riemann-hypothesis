module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.Foundations.ExistsUnitaryMulTriangular
public import Formalism.BranchSandwichDivisors.BranchIsometryProofs.BranchScale
public import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
public import Formalism.GradedWeylDivisibility.FinalB
public import Formalism.GradedWeylDivisibility.FinalC
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LDrowLemmas
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LHwinLemmas
public import Formalism.GradedWeylDivisibility.StatementA
public import Init.Classical
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Fin.Basic
public import Init.Data.Int.Basic
public import Init.Data.Int.Lemmas
public import Init.Data.Int.Order
public import Init.Data.Zero
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.Order.Group.Defs
public import Mathlib.Algebra.Order.Group.Int
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Ring.Unbundled.Basic
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Algebra.Order.Star.Int
public import Mathlib.Algebra.Order.ZeroLEOne
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Empty
public import Mathlib.Data.Finset.Filter
public import Mathlib.Data.Finset.Lattice.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Cast.Order.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Logic.Function.Defs
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Fin.Basic
public import Mathlib.Order.Monotone.Defs
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Tactic.Zify

@[expose] public section

open GlobalTheory.DualWeyl MvPolynomial NumberField Formalism.GradedWeylDivisibility

namespace GlobalTheory.DualWeyl

theorem rowDeg_dominated_of_mem_nabla {K : Type} [Field K] {N : ℕ} (la : Fin N → ℕ) (f : Pol N K)
    (hf : f ∈ nabla la K) : ∀ m ∈ f.support,
      (∀ k : ℕ, (∑ a : Fin N with a.val < k, rowDeg m a) ≤ ∑ t : Fin N with t.val < k, la t) ∧
      ∑ a : Fin N, rowDeg m a = ∑ t : Fin N, la t := by
  classical
  unfold nabla at hf
  rw [standardMonomialSpanDomain K N N la] at hf
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, sz, hsz, I, hshape, rfl⟩ := hx
    intro m hm
    have h := bidetDominance K N N k sz hsz I m hm
    rw [hshape] at h
    exact h
  | zero =>
    intro m hm
    simp at hm
  | add x y _ _ hx hy =>
    intro m hm
    rcases Finset.mem_union.mp (support_add hm) with h | h
    · exact hx m h
    · exact hy m h
  | smul c x _ hx =>
    intro m hm
    exact hx m (support_smul hm)

theorem eq_evalAt_one_smul_extremal_of_rowWeight (K : Type) [Field K] [Infinite K] (N : ℕ) (la : Fin N → ℕ)
    (hla : Antitone la) (f : Pol N K) (hf : f ∈ nabla la K)
    (hw' : IsWeightedHomogeneous (Formalism.GradedWeylDivisibility.rowW N N) f la) : f = evalAt 1 f • extremal la K := by
  obtain ⟨c, hc⟩ : ∃ c : K, f = c • extremal la K := by
    apply hwLine K N N le_rfl la hla f hf
    intro a b hab k hk
    by_contra hne
    have hmem := rowDivStable K N N la a b k f hf
    have hht : IsWeightedHomogeneous (lhwinHt N N) f (∑ a : Fin N, (a.val : ℤ) * (la a : ℤ)) := by
      intro d hd
      rw [lhwin_weight_ht, hw' hd]
    have hsh := lhwin_rowDiv_shift K _ a b k f hht
    obtain ⟨d, hd⟩ := ne_zero_iff.mp hne
    have e := hsh hd
    rw [lhwin_weight_ht] at e
    simp only [ldrow_weight_rowW] at e
    have dom := rowDeg_dominated_of_mem_nabla la _ hmem d (mem_support_iff.mpr hd)
    have hle := Formalism.BranchingDeterminantCap.bs_height_le N (rowDeg d) la dom.1 dom.2
    have hab' : (a.val : ℤ) - b.val ≤ -1 := by
      have : a.val < b.val := hab
      omega
    have hk' : (1 : ℤ) ≤ k := by exact_mod_cast hk
    nlinarith
  have h1 : evalAt 1 f = c := by
    rw [hc, map_smul, evalAt_one_extremal, smul_eq_mul, mul_one]
  rw [h1]
  exact hc

end GlobalTheory.DualWeyl
