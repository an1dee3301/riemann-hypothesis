module

public import Mathlib
public import Batteries.Logic
public import Init.Classical
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.List.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Nat.Lemmas
public import Init.Data.NeZero
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Pi
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Basic
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Algebra.Order.IsBotOne
public import Mathlib.Algebra.Order.Monoid.Canonical.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Monoid.Unbundled.WithTop
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Linear
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Module.Multilinear.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Complex.BigOperators
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.ENat.Basic
public import Mathlib.Data.ENat.Defs
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Empty
public import Mathlib.Data.Finset.Range
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Cast.Order.Basic
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Notation
public import Mathlib.Order.TypeTags
public import Mathlib.Order.WithBot
public import Mathlib.Tactic.FieldSimp.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.Positivity.Core
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Algebra.Module.Multilinear.Basic
public import Mathlib.Topology.Algebra.Module.Multilinear.Topology
public import Mathlib.Topology.Algebra.UniformMulAction
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.MetricSpace.Algebra
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open scoped ContDiff

namespace GlobalTheory.PolyOfDeriv

theorem taylor_of_chain (N : ℕ) : ∀ (G : ℕ → ℝ → ℂ) (_ : ∀ k t, HasDerivAt (G k) (G (k+1) t) t)
    (_ : G N = 0) (t : ℝ),
    G 0 t = ∑ k ∈ Finset.range N, G k 0 * ((t ^ k / k.factorial : ℝ) : ℂ) := by
  induction N with
  | zero => intro G _ hN t; simp [hN]
  | succ N ih =>
    intro G hG hN t
    have h1 : ∀ s, G 1 s = ∑ k ∈ Finset.range N, G (k+1) 0 * ((s ^ k / k.factorial : ℝ) : ℂ) :=
      fun s => ih (fun k => G (k+1)) (fun k t => hG (k+1) t) hN s
    have hm : ∀ (k : ℕ) (s : ℝ), HasDerivAt
        (fun s : ℝ => ((s ^ (k+1) / (k+1).factorial : ℝ) : ℂ))
        ((s ^ k / k.factorial : ℝ) : ℂ) s := by
      intro k s
      have h := (hasDerivAt_pow (k+1) s).div_const ((k+1).factorial : ℝ)
      have e : ((k+1 : ℕ) : ℝ) * s ^ (k + 1 - 1) / ((k+1).factorial : ℝ) = s ^ k / k.factorial := by
        rw [Nat.factorial_succ, Nat.add_sub_cancel, Nat.cast_mul]
        have : ((k+1 : ℕ) : ℝ) ≠ 0 := by positivity
        have : ((k.factorial : ℕ) : ℝ) ≠ 0 := by positivity
        field_simp
      rw [e] at h
      exact h.ofReal_comp
    have hH : ∀ s, HasDerivAt (fun s => G 0 s - ∑ k ∈ Finset.range N,
        G (k+1) 0 * ((s ^ (k+1) / (k+1).factorial : ℝ) : ℂ)) 0 s := by
      intro s
      have h2 : HasDerivAt (fun s : ℝ => ∑ k ∈ Finset.range N,
          G (k+1) 0 * ((s ^ (k+1) / (k+1).factorial : ℝ) : ℂ)) (G 1 s) s := by
        rw [h1 s]
        exact HasDerivAt.fun_sum fun k _ => (hm k s).const_mul _
      have h3 := (hG 0 s).fun_sub h2
      rwa [zero_add, sub_self] at h3
    have hc := is_const_of_deriv_eq_zero (fun s => (hH s).differentiableAt)
      (fun s => (hH s).deriv) t 0
    rw [Finset.sum_range_succ']
    simp only [ne_eq, Nat.add_eq_zero_iff, one_ne_zero, and_false, not_false_eq_true, zero_pow,
      zero_div, Complex.ofReal_zero, mul_zero, Finset.sum_const_zero, sub_zero] at hc
    rw [← hc]
    simp

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem hasDerivAt_iter {u : E → ℂ} (hu : ContDiff ℝ ∞ u) (k : ℕ) (y x : E) (t : ℝ) :
    HasDerivAt (fun t : ℝ => iteratedFDeriv ℝ k u (y + t • x) (fun _ => x))
      (iteratedFDeriv ℝ (k+1) u (y + t • x) (fun _ => x)) t := by
  have hk : (k : WithTop ℕ∞) < ∞ := by exact_mod_cast ENat.coe_lt_top k
  have hd := ((hu.differentiable_iteratedFDeriv hk) (y + t • x)).hasFDerivAt
  have hl : HasDerivAt (fun t : ℝ => y + t • x) x t := by
    simpa using ((hasDerivAt_id t).smul_const x).const_add y
  have h1 := hd.comp_hasDerivAt t hl
  have h2 := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => E) ℂ
    (fun _ => x)).hasFDerivAt.comp_hasDerivAt t h1
  rw [iteratedFDeriv_succ_apply_left]
  exact h2

theorem foldr_replicate {u : E → ℂ} (hu : ContDiff ℝ ∞ u) (x : E) (k : ℕ) :
    (List.replicate k x).foldr
      (fun y g => fun z => deriv (fun t : ℝ => g (z + t • y)) 0) u
      = fun y => iteratedFDeriv ℝ k u y (fun _ => x) := by
  induction k with
  | zero => funext y; simp
  | succ k ih =>
    rw [List.replicate_succ, List.foldr_cons, ih]
    funext y
    have := (hasDerivAt_iter hu k y x 0).deriv
    simpa using this

theorem multilinear_diag_poly {ι : Type} [Fintype ι] [DecidableEq ι] {k : ℕ}
    (M : ContinuousMultilinearMap ℝ (fun _ : Fin k => ι → ℝ) ℂ) :
    ∃ q : MvPolynomial ι ℂ, ∀ x : ι → ℝ,
      M (fun _ => x) = MvPolynomial.eval (fun i => (x i : ℂ)) q := by
  refine ⟨∑ r : Fin k → ι, MvPolynomial.C (M (fun j => Pi.single (r j) (1:ℝ))) *
    ∏ j, MvPolynomial.X (r j), ?_⟩
  intro x
  have hx : (fun _ : Fin k => x) = fun _ => ∑ i, x i • (Pi.single i (1:ℝ) : ι → ℝ) := by
    funext _; ext l; simp [Pi.single_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hx, M.map_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, MvPolynomial.eval_C, map_prod, MvPolynomial.eval_X]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [M.map_smul_univ (fun j => x (r j)) (fun j => Pi.single (r j) 1)]
  rw [Complex.real_smul, Complex.ofReal_prod, mul_comm]

theorem eq_eval_of_dirDeriv_vanish : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ)
    (u : (ι → ℝ) → ℂ), ContDiff ℝ ∞ u →
    (∀ L : List (ι → ℝ), L.length = N →
      L.foldr (fun y g => fun x => deriv (fun t : ℝ => g (x + t • y)) 0) u = 0) →
    ∃ p : MvPolynomial ι ℂ, ∀ x, u x = MvPolynomial.eval (fun i => (x i : ℂ)) p := by
  intro ι _ _ N u hu hL
  choose q hq using fun k => multilinear_diag_poly (iteratedFDeriv ℝ k u 0)
  refine ⟨∑ k ∈ Finset.range N, MvPolynomial.C ((k.factorial : ℂ)⁻¹) * q k, ?_⟩
  intro x
  have hrep := hL (List.replicate N x) List.length_replicate
  rw [foldr_replicate hu] at hrep
  have key := taylor_of_chain N (fun k t => iteratedFDeriv ℝ k u (0 + t • x) (fun _ => x))
    (fun k t => hasDerivAt_iter hu k 0 x t) (by funext t; exact congrFun hrep _) 1
  simp only [zero_add, one_smul, zero_smul, iteratedFDeriv_zero_apply, hq] at key
  rw [key]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, MvPolynomial.eval_C]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_comm]; simp

end GlobalTheory.PolyOfDeriv
