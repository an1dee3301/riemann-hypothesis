module

public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GaussianPlaneIntegrals.ContinuousPhi
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GaussianPlaneIntegrals.AssemblyAlt
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GaussianPlaneIntegrals.IntegralHkDiag
public import Init.BinderNameHint
public import Init.Core
public import Init.Data.Sum.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Init.Tactics
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
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
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Algebra.Star.BigOperators
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Complex.BigOperators
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Prod.Basic
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

open MeasureTheory MvPolynomial Module
open scoped ComplexConjugate

namespace PositivityTheory.Rg.Sw.FFTSteps.PosProof

variable {ι A B : Type} [Fintype ι] [DecidableEq ι] [Fintype A] [Fintype B]

theorem gw_prod (z : Sg ι A B → ℂ) : Complex.exp (-(∑ s, ‖z s‖ ^ 2 : ℝ)) = ∏ s, e1 (z s) := by
  simp only [e1]
  rw [← Complex.exp_sum]
  congr 1
  push_cast
  simp [Finset.sum_neg_distrib]

def mon (m : Sg ι A B →₀ ℕ) (z : Sg ι A B → ℂ) : ℂ := ∏ s, z s ^ m s

theorem mon_prod (m m' : Sg ι A B →₀ ℕ) (z : Sg ι A B → ℂ) :
    mon m z * star (mon m' z) * Complex.exp (-(∑ s, ‖z s‖ ^ 2 : ℝ)) = ∏ s, hk (m s) (m' s) (z s) := by
  rw [gw_prod]
  simp only [mon, hk, Complex.star_def, map_prod, map_pow, Finset.prod_mul_distrib]

theorem integrable_mon (m m' : Sg ι A B →₀ ℕ) :
    Integrable (fun z : Sg ι A B → ℂ => mon m z * star (mon m' z) * Complex.exp (-(∑ s, ‖z s‖ ^ 2 : ℝ))) := by
  simp_rw [mon_prod]
  have := Integrable.fintype_prod (f := fun s => hk (m s) (m' s)) (μ := fun _ => (volume : Measure ℂ))
    (fun s => integrable_hk _ _)
  rwa [← volume_pi] at this

theorem integral_mon (m m' : Sg ι A B →₀ ℕ) :
    ∫ z : Sg ι A B → ℂ, mon m z * star (mon m' z) * Complex.exp (-(∑ s, ‖z s‖ ^ 2 : ℝ)) =
      ∏ s, ∫ w, hk (m s) (m' s) w := by
  simp_rw [mon_prod]
  exact integral_fintype_prod_volume_eq_prod (fun s w => hk (m s) (m' s) w)

theorem integral_mon_ne (m m' : Sg ι A B →₀ ℕ) (h : m ≠ m') :
    ∫ z : Sg ι A B → ℂ, mon m z * star (mon m' z) * Complex.exp (-(∑ s, ‖z s‖ ^ 2 : ℝ)) = 0 := by
  rw [integral_mon]
  obtain ⟨s, hs⟩ : ∃ s, m s ≠ m' s := by
    by_contra hc
    push Not at hc
    exact h (Finsupp.ext hc)
  exact Finset.prod_eq_zero (Finset.mem_univ s) (integral_hk_ne _ _ hs)

theorem integral_mon_self (m : Sg ι A B →₀ ℕ) :
    ∫ z : Sg ι A B → ℂ, mon m z * star (mon m z) * Complex.exp (-(∑ s, ‖z s‖ ^ 2 : ℝ)) =
      ((∏ s, jr (m s) : ℝ) : ℂ) := by
  rw [integral_mon]
  push_cast
  exact Finset.prod_congr rfl fun s _ => integral_hk_diag _

def kap (d : ι → ℝ) : Sg ι A B → ℝ := Sum.elim (fun _ => 1) (fun y => d y.1)

def lam (d : ι → ℝ) (m : Sg ι A B →₀ ℕ) : ℝ := ∏ s, kap d s ^ m s

theorem Phi_diag (d : ι → ℝ) (z : Sg ι A B → ℂ) :
    Phi (Matrix.diagonal fun i => (d i : ℂ)) z = fun s => (kap d s : ℂ) * z s := by
  funext s
  rcases s with x | ⟨i, b⟩
  · simp [Phi, kap]
  · simp [Phi, kap, Matrix.diagonal_apply]

theorem gip_diag (d : ι → ℝ) (g : PV ι A B) :
    gip (sub 1 (Matrix.diagonal fun i => (d i : ℂ)) g) g =
      ((∑ m ∈ g.support, Complex.normSq (g.coeff m) * lam d m * ∏ s, jr (m s) : ℝ) : ℂ) := by
  unfold gip
  have hpt : ∀ z : Sg ι A B → ℂ,
      eval z (sub 1 (Matrix.diagonal fun i => (d i : ℂ)) g) * star (eval z g) * Complex.exp (-(∑ s, ‖z s‖ ^ 2 : ℝ)) =
        ∑ m ∈ g.support, ∑ m' ∈ g.support, (g.coeff m * (lam d m : ℂ) * star (g.coeff m')) *
          (mon m z * star (mon m' z) * Complex.exp (-(∑ s, ‖z s‖ ^ 2 : ℝ))) := by
    intro z
    rw [eval_sub, Phi_diag, MvPolynomial.eval_eq', MvPolynomial.eval_eq']
    have hl : ∀ m : Sg ι A B →₀ ℕ, ∏ s, ((kap d s : ℂ) * z s) ^ m s = (lam d m : ℂ) * mon m z := by
      intro m
      simp only [mul_pow, Finset.prod_mul_distrib, lam, mon]
      push_cast
      rfl
    simp_rw [hl]
    rw [star_sum, Finset.sum_mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun m' _ => ?_
    have hmon : (∏ i, z i ^ m' i) = mon m' z := rfl
    try simp only [star_mul']
    try rw [hmon]
    ring
  simp_rw [hpt]
  have hint : ∀ m m' : Sg ι A B →₀ ℕ, Integrable fun z : Sg ι A B → ℂ => mon m z * star (mon m' z) * Complex.exp (-(∑ s, ‖z s‖ ^ 2 : ℝ)) :=
    integrable_mon
  rw [MeasureTheory.integral_finsetSum _ fun m _ => MeasureTheory.integrable_finsetSum _ fun m' _ => (hint m m').const_mul _]
  rw [Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [MeasureTheory.integral_finsetSum _ fun m' _ => (hint m m').const_mul _]
  simp_rw [integral_const_mul]
  rw [Finset.sum_eq_single_of_mem m hm fun m' _ hne => by rw [integral_mon_ne m m' hne.symm, mul_zero]]
  rw [integral_mon_self]
  have hc : ((Complex.normSq (g.coeff m) : ℝ) : ℂ) = g.coeff m * star (g.coeff m) := by
    rw [Complex.star_def, Complex.mul_conj]
  rw [Complex.ofReal_mul, Complex.ofReal_mul, hc]
  ring

end PositivityTheory.Rg.Sw.FFTSteps.PosProof
