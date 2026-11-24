module

public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GaussianPlaneIntegrals.SecLineA
public import Development.Core20Slim.Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.MatrixInfinitySpan.RealMatch
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.NullSec
public import Init.ByCases
public import Init.Core
public import Init.Data.Bool
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Order.Lemmas
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Ring.Unbundled.Basic
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Algebra.Star.BigOperators
public import Mathlib.Analysis.CStarAlgebra.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.Real.Star
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Filter
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.RelClasses
public import Mathlib.Tactic.CancelDenoms.Core
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Positivity.Core
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.MvPolynomial
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Star
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

open MeasureTheory MvPolynomial

namespace PositivityTheory.Rg.Sw.FFTSteps.SecondLineEstimates

variable {m n : ℕ}

lemma continuous_evX (P : PX m n) : Continuous (fun x : Fin m → Fin n → ℂ => evX P x) := by
  unfold evX
  refine (MvPolynomial.continuous_eval P).comp (continuous_pi fun k => ?_)
  by_cases h : k.2.2
  · simp only [h, if_true]
    exact continuous_star.comp ((continuous_apply k.2.1).comp (continuous_apply k.1))
  · simp only [h]
    exact (continuous_apply k.2.1).comp (continuous_apply k.1)

lemma evX_bound (P : PX m n) : ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ x, ‖evX P x‖ ≤ C * (1 + sq x) ^ N := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    exact ⟨‖a‖, norm_nonneg _, 0, fun x => by simp [evX]⟩
  | add p q hp hq =>
    obtain ⟨C1, h1, N1, hp⟩ := hp
    obtain ⟨C2, h2, N2, hq⟩ := hq
    refine ⟨C1 + C2, by positivity, max N1 N2, fun x => ?_⟩
    have hs : 1 ≤ 1 + sq x := by linarith [sq_nonneg' x]
    have e1 : (1 + sq x) ^ N1 ≤ (1 + sq x) ^ (max N1 N2) := pow_le_pow_right₀ hs (le_max_left _ _)
    have e2 : (1 + sq x) ^ N2 ≤ (1 + sq x) ^ (max N1 N2) := pow_le_pow_right₀ hs (le_max_right _ _)
    calc ‖evX (p + q) x‖ = ‖evX p x + evX q x‖ := by simp [evX]
      _ ≤ ‖evX p x‖ + ‖evX q x‖ := norm_add_le _ _
      _ ≤ C1 * (1 + sq x) ^ N1 + C2 * (1 + sq x) ^ N2 := add_le_add (hp x) (hq x)
      _ ≤ C1 * (1 + sq x) ^ (max N1 N2) + C2 * (1 + sq x) ^ (max N1 N2) :=
          add_le_add (mul_le_mul_of_nonneg_left e1 h1) (mul_le_mul_of_nonneg_left e2 h2)
      _ = (C1 + C2) * (1 + sq x) ^ (max N1 N2) := by ring
  | mul_X p k hp =>
    obtain ⟨C, h, N, hp⟩ := hp
    refine ⟨C, h, N + 1, fun x => ?_⟩
    have hk : ‖(if k.2.2 then star (x k.1 k.2.1) else x k.1 k.2.1)‖ ≤ 1 + sq x := by
      split_ifs
      · rw [norm_star]; exact coord_le x _ _
      · exact coord_le x _ _
    calc ‖evX (p * X k) x‖ = ‖evX p x‖ * ‖(if k.2.2 then star (x k.1 k.2.1) else x k.1 k.2.1)‖ := by
          rw [evX, map_mul, eval_X, norm_mul]; rfl
      _ ≤ C * (1 + sq x) ^ N * (1 + sq x) :=
          mul_le_mul (hp x) hk (norm_nonneg _) (by have := sq_nonneg' x; positivity)
      _ = C * (1 + sq x) ^ (N + 1) := by ring

lemma gram_apply (ε : Fin m → Bool) (x : Fin m → Fin n → ℂ) (i j : Fin n) :
    gramX ε x i j = ∑ a, sgn ε a * (star (x a i) * x a j) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [gramX, Qp, Qb, evX, map_sub, map_sum, map_mul, eval_X]
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  cases h : ε a <;> simp [sgn, h]

lemma continuous_gram (ε : Fin m → Bool) (i j : Fin n) :
    Continuous (fun x : Fin m → Fin n → ℂ => gramX ε x i j) :=
  continuous_evX _

lemma norm_gram_le (ε : Fin m → Bool) (x : Fin m → Fin n → ℂ) (i j : Fin n) : ‖gramX ε x i j‖ ≤ sq x := by
  rw [gram_apply]
  have hsg : ∀ a, ‖sgn ε a‖ = 1 := fun a => by unfold sgn; split_ifs <;> simp
  calc ‖∑ a, sgn ε a * (star (x a i) * x a j)‖ ≤ ∑ a, ‖sgn ε a * (star (x a i) * x a j)‖ := norm_sum_le _ _
    _ = ∑ a, ‖x a i‖ * ‖x a j‖ := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [norm_mul, norm_mul, hsg, norm_star, one_mul]
    _ ≤ ∑ a, (‖x a i‖ ^ 2 + ‖x a j‖ ^ 2) / 2 := by
        refine Finset.sum_le_sum fun a _ => ?_
        nlinarith [sq_nonneg (‖x a i‖ - ‖x a j‖)]
    _ = ((∑ a, ‖x a i‖ ^ 2) + ∑ a, ‖x a j‖ ^ 2) / 2 := by rw [← Finset.sum_add_distrib, Finset.sum_div]
    _ ≤ (sq x + sq x) / 2 := by gcongr <;> exact col_sq_le x _
    _ = sq x := by ring

lemma trace_eq (ε : Fin m → Bool) (b : Matrix (Fin n) (Fin n) ℂ) (x : Fin m → Fin n → ℂ) :
    (b * gramX ε x).trace = ∑ i, ∑ j, b i j * gramX ε x j i := by
  simp [Matrix.trace, Matrix.mul_apply]

lemma continuous_trace (ε : Fin m → Bool) (b : Matrix (Fin n) (Fin n) ℂ) :
    Continuous (fun x : Fin m → Fin n → ℂ => (b * gramX ε x).trace) := by
  simp only [trace_eq]
  exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    continuous_const.mul (continuous_gram ε j i)

def kb (b : Matrix (Fin n) (Fin n) ℂ) : ℝ := ∑ i, ∑ j, ‖b i j‖

lemma kb_nonneg (b : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ kb b := by unfold kb; positivity

lemma norm_trace_le (ε : Fin m → Bool) (b : Matrix (Fin n) (Fin n) ℂ) (x : Fin m → Fin n → ℂ) :
    ‖(b * gramX ε x).trace‖ ≤ kb b * sq x := by
  rw [trace_eq, kb, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_gram_le ε x j i) (norm_nonneg _)

lemma trace_im (ε : Fin m → Bool) (b : Matrix (Fin n) (Fin n) ℂ) (hb : b.IsHermitian) (x : Fin m → Fin n → ℂ) :
    ((b * gramX ε x).trace).im = 0 := by
  have hg : ∀ i j, star (gramX ε x j i) = gramX ε x i j := by
    intro i j
    rw [gram_apply, gram_apply, star_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    have hs : star (sgn ε a) = sgn ε a := by unfold sgn; split_ifs <;> simp
    rw [star_mul', star_mul', hs, star_star]; ring
  have : star ((b * gramX ε x).trace) = (b * gramX ε x).trace := by
    rw [trace_eq, star_sum]
    simp_rw [star_sum, star_mul', hg]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hb.apply]
  exact Complex.conj_eq_iff_im.1 this

end PositivityTheory.Rg.Sw.FFTSteps.SecondLineEstimates
