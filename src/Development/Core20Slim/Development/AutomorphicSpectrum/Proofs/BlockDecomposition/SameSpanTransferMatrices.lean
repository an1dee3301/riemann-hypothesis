module

public import Mathlib
public import Development.Core20Slim.Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.EisCellsDefs
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsBlockMatrixTwoByTwoFinEq
public import Init.Classical
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Span.Defs

@[expose] public section

open scoped Matrix
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions.EC

namespace GlobalTheory.CompanionTheory.BruhatCoeffs

theorem exists_coeff_matrices_of_span_eq {K : Type} [Field K] {n r : ℕ}
    (C : Matrix (Fin n) (Fin n) K) (c : Matrix (Fin r) (Fin n) K)
    (hc : LinearIndependent K c)
    (hs : Submodule.span K (Set.range c) = Submodule.span K (Set.range C)) :
    ∃ (T : Matrix (Fin n) (Fin r) K) (L : Matrix (Fin r) (Fin n) K),
      C = T * c ∧ c = L * C ∧ L * T = 1 := by
  have hT0 : ∀ j, ∃ t : Fin r → K, ∑ i, t i • c i = C j := by
    intro j
    have hj : C j ∈ Submodule.span K (Set.range c) := by
      rw [hs]
      exact Submodule.subset_span (Set.mem_range_self j)
    exact (Submodule.mem_span_range_iff_exists_fun K).mp hj
  have hL0 : ∀ i, ∃ t : Fin n → K, ∑ j, t j • C j = c i := by
    intro i
    have hi : c i ∈ Submodule.span K (Set.range C) := by
      rw [← hs]
      exact Submodule.subset_span (Set.mem_range_self i)
    exact (Submodule.mem_span_range_iff_exists_fun K).mp hi
  obtain ⟨T, hT⟩ : ∃ T : Matrix (Fin n) (Fin r) K, ∀ j, ∑ i, T j i • c i = C j :=
    ⟨fun j => (hT0 j).choose, fun j => (hT0 j).choose_spec⟩
  obtain ⟨L, hL⟩ : ∃ L : Matrix (Fin r) (Fin n) K, ∀ i, ∑ j, L i j • C j = c i :=
    ⟨fun i => (hL0 i).choose, fun i => (hL0 i).choose_spec⟩
  have hCT : C = T * c := by
    ext j k
    rw [← hT j, Matrix.mul_apply]
    simp [Finset.sum_apply]
  have hcL : c = L * C := by
    ext i k
    rw [← hL i, Matrix.mul_apply]
    simp [Finset.sum_apply]
  refine ⟨T, L, hCT, hcL, ?_⟩
  have hLT : L * T * c = c := by rw [Matrix.mul_assoc, ← hCT, ← hcL]
  have hz0 : (L * T - 1) * c = 0 := by rw [Matrix.sub_mul, hLT, Matrix.one_mul, sub_self]
  have hc' := Fintype.linearIndependent_iff.mp hc
  ext i0 i
  have hrow : ∑ i, (L * T - 1 : Matrix (Fin r) (Fin r) K) i0 i • c i = 0 := by
    funext k
    have h0 := congrFun (congrFun hz0 i0) k
    rw [Matrix.mul_apply] at h0
    simpa [Finset.sum_apply] using h0
  have h1 : (L * T - 1 : Matrix (Fin r) (Fin r) K) i0 i = 0 := hc' (fun i => (L * T - 1 : Matrix (Fin r) (Fin r) K) i0 i) hrow i
  rwa [Matrix.sub_apply, sub_eq_zero] at h1

end GlobalTheory.CompanionTheory.BruhatCoeffs
