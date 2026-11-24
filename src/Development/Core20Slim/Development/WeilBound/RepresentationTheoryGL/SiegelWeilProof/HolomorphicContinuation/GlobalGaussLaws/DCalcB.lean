module

public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DCalcA
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobData
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.FourierZeroN
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
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.IsApply
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
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
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Complex.BigOperators
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.MetricSpace.Algebra
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

open Matrix MvPolynomial

namespace PositivityTheory.Rg.Sw.Glob

namespace DCalcBH

open DCalcH

variable {m n : ℕ}

theorem norm_vS (u : Fin m → Fin n → ℂ) (X : Fin n → ℝ) (s : ℝ) (a : Fin m) (j : Fin n) :
    ‖vS u X s a j‖ ^ 2 = ‖u a j‖ ^ 2 * Real.exp (s * X j) ^ 2 := by
  simp only [DCalcH.vS, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]

def nS (u : Fin m → Fin n → ℂ) (X : Fin n → ℝ) (s : ℝ) : ℝ := ∑ a, ∑ j, ‖u a j‖ ^ 2 * Real.exp (s * X j) ^ 2

theorem gs_vS (c : ℝ) (u : Fin m → Fin n → ℂ) (X : Fin n → ℝ) (s : ℝ) :
    gs c (vS u X s) = Complex.exp (((-(c * nS u X s)) : ℝ) : ℂ) := by
  simp only [gs, nS, norm_vS, Complex.ofReal_neg]

theorem nS_hasDeriv (u : Fin m → Fin n → ℂ) (X : Fin n → ℝ) (s : ℝ) :
    HasDerivAt (nS u X) (∑ a, ∑ j, 2 * X j * ‖vS u X s a j‖ ^ 2) s := by
  have h : ∀ a j, HasDerivAt (fun s => ‖u a j‖ ^ 2 * Real.exp (s * X j) ^ 2)
      (2 * X j * ‖vS u X s a j‖ ^ 2) s := by
    intro a j
    rw [norm_vS]
    have h1 : HasDerivAt (fun s : ℝ => s * X j) (X j) s := by
      simpa using (hasDerivAt_id s).mul_const (X j)
    refine (((h1.exp).pow 2).const_mul (‖u a j‖ ^ 2)).congr_deriv ?_
    rw [show (2 : ℕ) - 1 = 1 from rfl, pow_one]
    push_cast
    ring
  have h3 := HasDerivAt.sum (u := Finset.univ) fun a _ => HasDerivAt.sum (u := Finset.univ) fun j _ => h a j
  have e : nS u X = ∑ a, ∑ j, fun s : ℝ => ‖u a j‖ ^ 2 * Real.exp (s * X j) ^ 2 := by
    ext y
    simp [nS, Finset.sum_apply]
  rw [e]
  exact h3

theorem gs_hasDeriv (c : ℝ) (u : Fin m → Fin n → ℂ) (X : Fin n → ℝ) (s : ℝ) :
    HasDerivAt (fun s : ℝ => gs c (vS u X s))
      (gs c (vS u X s) * (-(2 * c : ℂ) * ∑ a, ∑ j, (X j : ℂ) * ((‖vS u X s a j‖ ^ 2 : ℝ) : ℂ))) s := by
  simp_rw [gs_vS]
  have h := ((nS_hasDeriv u X s).const_mul c).neg.ofReal_comp.cexp
  refine h.congr_deriv ?_
  congr 1
  push_cast
  rw [neg_mul]
  congr 1
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

def fF (c : ℝ) (X : Fin n → ℝ) (P : PX m n) (u : Fin m → Fin n → ℂ) (s : ℝ) : ℂ :=
  ((Real.exp (s * (m : ℝ) * ∑ j, X j) : ℝ) : ℂ) * fP c P (vS u X s)

theorem fF_hasDeriv (c : ℝ) (X : Fin n → ℝ) (P : PX m n) (u : Fin m → Fin n → ℂ) (s : ℝ) :
    HasDerivAt (fF c X P u) (fF c X (dil c X P) u s) s := by
  have he : HasDerivAt (fun s : ℝ => ((Real.exp (s * (m : ℝ) * ∑ j, X j) : ℝ) : ℂ))
      ((((m : ℝ) * ∑ j, X j : ℝ) : ℂ) * ((Real.exp (s * (m : ℝ) * ∑ j, X j) : ℝ) : ℂ)) s := by
    have := hasDerivAt_expX ((m : ℝ) * ∑ j, X j) s
    simp only [mul_assoc] at this ⊢
    exact this
  have h := he.mul ((eval_hasDeriv P u X s).mul (gs_hasDeriv c u X s))
  unfold fF fP
  have efun : (fun s : ℝ => ((Real.exp (s * (m : ℝ) * ∑ j, X j) : ℝ) : ℂ) * (evX P (vS u X s) * gs c (vS u X s))) =
      fun s => ((Real.exp (s * (m : ℝ) * ∑ j, X j) : ℝ) : ℂ) * (evX P (vS u X s) * gs c (vS u X s)) := rfl
  refine h.congr_deriv ?_
  simp only [Pi.mul_apply]
  rw [evX_dil]
  push_cast
  ring

theorem fF_iter (c : ℝ) (X : Fin n → ℝ) (u : Fin m → Fin n → ℂ) (r : ℕ) :
    iteratedDeriv r (fF c X 1 u) = fF c X ((dil c X ^ r) 1) u := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [iteratedDeriv_succ, ih]
    funext s
    rw [(fF_hasDeriv c X ((dil c X ^ r) 1) u s).deriv, pow_succ', Module.End.mul_apply]

end DCalcBH

end PositivityTheory.Rg.Sw.Glob
