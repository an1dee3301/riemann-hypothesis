module

public import Mathlib
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.GaussS
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.GBaseB
public import Development.Core20Slim.Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.MatrixInfinitySpan.RealMatch
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.GramXApply
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.EvXTemperate
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.NullSec
public import Init.Core
public import Init.Data.Bool
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
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
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Complex.BigOperators
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Filter
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

open MeasureTheory Complex Matrix MvPolynomial

namespace PositivityTheory.Rg.Sw.WR.G

open PositivityTheory.Rg.Sw

variable {m n : ℕ}

namespace GB

def sgnR (ε : Fin m → Bool) (a : Fin m) : ℝ := if ε a then 1 else -1

theorem sgn_eq (ε : Fin m → Bool) (a : Fin m) : sgn ε a = ((sgnR ε a : ℝ) : ℂ) := by
  unfold sgn sgnR; split_ifs <;> simp

theorem evX_Qb (ε : Fin m → Bool) (bb : Bool) (i j : Fin n) (x : Fin m → Fin n → ℂ) :
    evX (Qb ε bb i j) x = ∑ a ∈ Finset.univ.filter (fun a => ε a = bb), star (x a i) * x a j := by
  simp [evX, Qb]

theorem gramX_apply (ε : Fin m → Bool) (x : Fin m → Fin n → ℂ) (i j : Fin n) :
    gramX ε x i j = ∑ a, ((sgnR ε a : ℝ) : ℂ) * (star (x a i) * x a j) := by
  unfold gramX
  rw [Qp, evX, map_sub, ← evX, ← evX, evX_Qb, evX_Qb, Finset.sum_filter, Finset.sum_filter,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  unfold sgnR
  cases h : ε a <;> simp

theorem trace_gram (ε : Fin m → Bool) (b : Matrix (Fin n) (Fin n) ℂ) (x : Fin m → Fin n → ℂ) :
    (b * gramX ε x).trace = ∑ a, ((sgnR ε a : ℝ) : ℂ) * ∑ i, ∑ j, star (x a i) * bᵀ i j * x a j := by
  have L : (b * gramX ε x).trace =
      ∑ a, ∑ i, ∑ j, b i j * (((sgnR ε a : ℝ) : ℂ) * (star (x a j) * x a i)) := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, gramX_apply, Finset.mul_sum]
    calc (∑ i, ∑ j, ∑ a, b i j * (((sgnR ε a : ℝ) : ℂ) * (star (x a j) * x a i)))
        = ∑ i, ∑ a, ∑ j, b i j * (((sgnR ε a : ℝ) : ℂ) * (star (x a j) * x a i)) :=
          Finset.sum_congr rfl (fun i _ => Finset.sum_comm)
      _ = _ := Finset.sum_comm
  rw [L]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Matrix.transpose_apply]
  ring

theorem herm_transpose (b : Matrix (Fin n) (Fin n) ℂ) (hb : b.IsHermitian) : bᵀ.IsHermitian := by
  ext i j
  have := congrFun (congrFun hb j) i
  simp only [Matrix.conjTranspose_apply, Matrix.transpose_apply] at this ⊢
  rw [← this]

end GB

open GB in
theorem base : Base := by
  intro m n ε c t hc b hb
  unfold secN
  have hpt : ∀ x : Fin m → Fin n → ℂ, evX 1 x * gs c x * cexp (Complex.I * t * (b * gramX ε x).trace) =
      ∏ a, cexp (-(((c * ∑ k, ‖x a k‖ ^ 2 : ℝ)) : ℂ) +
        Complex.I * ((t * sgnR ε a : ℝ) : ℂ) * ∑ i, ∑ j, star (x a i) * bᵀ i j * x a j) := by
    intro x
    have h1 : evX (1 : PX m n) x = 1 := by simp [evX]
    rw [h1, one_mul, gs, ← Complex.exp_add, ← Complex.exp_sum, trace_gram]
    congr 1
    rw [Finset.sum_add_distrib]
    congr 1
    · push_cast
      rw [Finset.mul_sum, Finset.sum_neg_distrib]
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      push_cast
      ring
  simp_rw [hpt]
  rw [integral_fintype_prod_volume_eq_prod (fun a (r : Fin n → ℂ) => cexp (-(((c * ∑ k, ‖r k‖ ^ 2 : ℝ)) : ℂ) +
        Complex.I * ((t * sgnR ε a : ℝ) : ℂ) * ∑ i, ∑ j, star (r i) * bᵀ i j * r j))]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [GB.gauss_row c (t * sgnR ε a) hc bᵀ (herm_transpose b hb)]
  have e : Complex.I * ((t * sgnR ε a : ℝ) : ℂ) = Complex.I * t * sgn ε a := by
    rw [sgn_eq]; push_cast; ring
  rw [e]
  rfl

end PositivityTheory.Rg.Sw.WR.G
