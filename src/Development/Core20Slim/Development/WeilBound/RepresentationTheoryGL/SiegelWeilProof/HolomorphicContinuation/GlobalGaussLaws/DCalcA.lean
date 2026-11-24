module

public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DifferenceQuotientIsometryExchangeAlt
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobData
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.NullSec
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Submodule.LinearMap
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Basic
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.MetricSpace.Algebra
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

open Matrix MvPolynomial

namespace PositivityTheory.Rg.Sw.Glob

namespace DCalcH

variable {m n : ℕ}

def vS (u : Fin m → Fin n → ℂ) (X : Fin n → ℝ) (s : ℝ) : Fin m → Fin n → ℂ :=
  fun a j => u a j * (Real.exp (s * X j) : ℂ)

def crd (v : Fin m → Fin n → ℂ) (k : Fin m × Fin n × Bool) : ℂ := if k.2.2 then star (v k.1 k.2.1) else v k.1 k.2.1

theorem evX_eq (P : PX m n) (v : Fin m → Fin n → ℂ) : evX P v = MvPolynomial.eval (crd v) P := rfl

theorem crd_vS (u : Fin m → Fin n → ℂ) (X : Fin n → ℝ) (k : Fin m × Fin n × Bool) (s : ℝ) :
    crd (vS u X s) k = crd u k * ((Real.exp (s * X k.2.1) : ℝ) : ℂ) := by
  unfold crd vS
  split_ifs
  · rw [star_mul', Complex.star_def, Complex.conj_ofReal]
  · rfl

theorem hasDerivAt_expX (x s : ℝ) :
    HasDerivAt (fun s : ℝ => ((Real.exp (s * x) : ℝ) : ℂ)) ((x : ℂ) * ((Real.exp (s * x) : ℝ) : ℂ)) s := by
  have h := ((hasDerivAt_id s).mul_const x).exp
  simp only [id, one_mul] at h
  have h2 := h.ofReal_comp
  have e : ((x : ℂ) * ((Real.exp (s * x) : ℝ) : ℂ)) = ((Real.exp (s * x) * x : ℝ) : ℂ) := by push_cast; ring
  rw [e]
  exact h2

theorem crd_hasDeriv (u : Fin m → Fin n → ℂ) (X : Fin n → ℝ) (k : Fin m × Fin n × Bool) (s : ℝ) :
    HasDerivAt (fun s : ℝ => crd (vS u X s) k) ((X k.2.1 : ℂ) * crd (vS u X s) k) s := by
  have h := (hasDerivAt_expX (X k.2.1) s).const_mul (crd u k)
  have e1 : (fun s : ℝ => crd (vS u X s) k) = fun s => crd u k * ((Real.exp (s * X k.2.1) : ℝ) : ℂ) :=
    funext fun s => crd_vS u X k s
  rw [e1, crd_vS]
  exact h.congr_deriv (by ring)

theorem pderiv_mul_X (p : PX m n) (k i : Fin m × Fin n × Bool) :
    pderiv i (p * MvPolynomial.X k) = pderiv i p * MvPolynomial.X k + if i = k then p else 0 := by
  rw [Derivation.leibniz, pderiv_X, smul_eq_mul, smul_eq_mul]
  by_cases h : i = k
  · subst h; simp [add_comm, mul_comm]
  · simp [h, Ne.symm h, mul_comm]

theorem eval_hasDeriv (P : PX m n) (u : Fin m → Fin n → ℂ) (X : Fin n → ℝ) (s : ℝ) :
    HasDerivAt (fun s : ℝ => evX P (vS u X s))
      (∑ k, evX (pderiv k P) (vS u X s) * ((X k.2.1 : ℂ) * crd (vS u X s) k)) s := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    simp only [evX_eq, eval_C, pderiv_C, map_zero, zero_mul, Finset.sum_const_zero]
    exact hasDerivAt_const _ _
  | add p q hp hq =>
    simp only [evX_eq, map_add (f := _), add_mul, Finset.sum_add_distrib] at *
    exact hp.add hq
  | mul_X p k hp =>
    have h := hp.mul (crd_hasDeriv u X k s)
    simp only [evX_eq] at *
    have efun : (fun s : ℝ => eval (crd (vS u X s)) (p * MvPolynomial.X k)) =
        fun s => eval (crd (vS u X s)) p * crd (vS u X s) k := by
      funext s'; simp [eval_mul, eval_X]
    rw [efun]
    refine h.congr_deriv ?_
    symm
    set D : Fin m × Fin n × Bool → ℂ := fun i => (X i.2.1 : ℂ) * crd (vS u X s) i with hD
    calc (∑ i, eval (crd (vS u X s)) (pderiv i (p * MvPolynomial.X k)) * D i)
        = ∑ i, (eval (crd (vS u X s)) (pderiv i p) * D i * crd (vS u X s) k +
            (if i = k then eval (crd (vS u X s)) p * D i else 0)) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [pderiv_mul_X]
          split_ifs with hik
          · simp [eval_mul, eval_X]; ring
          · simp [eval_mul, eval_X]; ring
      _ = (∑ i, eval (crd (vS u X s)) (pderiv i p) * D i) * crd (vS u X s) k + eval (crd (vS u X s)) p * D k := by
          rw [Finset.sum_add_distrib, Finset.sum_mul, Finset.sum_ite_eq']
          simp

theorem crd_false (v : Fin m → Fin n → ℂ) (a : Fin m) (j : Fin n) : crd v (a, j, false) = v a j := rfl

theorem crd_true (v : Fin m → Fin n → ℂ) (a : Fin m) (j : Fin n) : crd v (a, j, true) = star (v a j) := rfl

theorem evX_dil (c : ℝ) (X : Fin n → ℝ) (P : PX m n) (v : Fin m → Fin n → ℂ) :
    evX (dil c X P) v = ((m : ℂ) * ∑ j, (X j : ℂ)) * evX P v +
      ∑ k, evX (pderiv k P) v * ((X k.2.1 : ℂ) * crd v k) -
      (2 * c : ℂ) * (∑ a, ∑ j, (X j : ℂ) * ((‖v a j‖ ^ 2 : ℝ) : ℂ)) * evX P v := by
  have hnorm : ∀ a j, ((‖v a j‖ ^ 2 : ℝ) : ℂ) = v a j * star (v a j) := by
    intro a j
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [dil, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.add_apply,
    LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.id_apply,
    Derivation.coeFn_coe, evX_eq, map_sum, map_add, map_sub, map_mul, MvPolynomial.smul_eval, eval_X, smul_eq_mul]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, crd_false, crd_true, hnorm]
  set E := (eval (crd v)) P with hE
  rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin m))) (t := (Finset.univ : Finset (Fin n)))
      (f := fun a j => (eval (crd v)) ((pderiv (a, j, true)) P) * ((X j : ℂ) * star (v a j)) +
        (eval (crd v)) ((pderiv (a, j, false)) P) * ((X j : ℂ) * v a j)),
    Finset.sum_comm (s := (Finset.univ : Finset (Fin m))) (t := (Finset.univ : Finset (Fin n)))
      (f := fun a j => (X j : ℂ) * (v a j * star (v a j)))]
  rw [Finset.mul_sum, Finset.sum_mul, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_add, Finset.mul_sum, Finset.mul_sum, Finset.sum_mul, add_sub_assoc, ← Finset.sum_sub_distrib]
  congr 1
  · ring
  · refine Finset.sum_congr rfl fun a _ => ?_
    ring

end DCalcH

end PositivityTheory.Rg.Sw.Glob
