module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.VacuumUnderAdelicPairModulusOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaSpanRationalTranslatesVacuum
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Init.Classical
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.GetElem
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Action.Units
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.Units.Equiv
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Units
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.Group.Multiset
public import Mathlib.Algebra.Order.ZeroLEOne
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Const
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Empty
public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Finsupp.Multiset
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Multiset.Basic
public import Mathlib.Data.Multiset.Defs
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.ConstMulAction
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Algebra.Module.Equiv.Basic
public import Mathlib.Topology.Algebra.Module.Multilinear.Basic
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField Polynomial
open scoped Pointwise nonZeroDivisors
open Formalism.L2.Host (HChar embTau)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FunObj GlobalTheory.FunObj.SqNum

namespace GlobalTheory.FunObj.NormUniq

variable {D : D7}

theorem wd_smul (T : Tor D) {N N' : ℕ} (x : VC D N N') (c : ℂ) (G : VC D N N' → ℂ) :
    Wd D T x (c • G) = c • Wd D T x G := by
  funext z
  simp only [Wd, U, Pi.smul_apply, smul_eq_mul]
  ring

theorem wd_add (T : Tor D) {N N' : ℕ} (x : VC D N N') (G G' : VC D N N' → ℂ) :
    Wd D T x (G + G') = Wd D T x G + Wd D T x G' := by
  funext z
  simp only [Wd, U, Pi.add_apply]
  ring

theorem applyAt0_smul {N N' : ℕ} (P : MvPolynomial (GL3Theta.Idx D N N') ℂ) {c : ℂ} (hc : c ≠ 0)
    (G : VC D N N' → ℂ) : GL3Theta.applyAt0 D P (c • G) = c * GL3Theta.applyAt0 D P G := by
  simp only [GL3Theta.applyAt0, Finset.mul_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  have : TaylorLogMetric.taylor D (c • G) α = c * TaylorLogMetric.taylor D G α := by
    unfold TaylorLogMetric.taylor
    let g : ℂ ≃L[ℂ] ℂ := ContinuousLinearEquiv.smulLeft (R₁ := ℂ) (M₁ := ℂ) (G := ℂˣ) (Units.mk0 c hc)
    have e : c • G = ⇑g ∘ G := by
      funext z; simp [g, ContinuousLinearEquiv.smulLeft, Units.smul_def]
    rw [e, ContinuousLinearEquiv.iteratedFDeriv_comp_left]
    simp [g, ContinuousLinearEquiv.smulLeft, Units.smul_def]
    ring
  rw [this]; ring

theorem tt_zero (T : Tor D) {N N' : ℕ} : (0 : VC D N N' → ℂ) ∈ TT D T N N' :=
  ⟨differentiable_const 0, 1, one_pos, fun x _ => by funext z; simp [Wd, U]⟩

theorem tt_add {T : Tor D} {N N' : ℕ} {F F' : VC D N N' → ℂ} (hF : F ∈ TT D T N N') (hF' : F' ∈ TT D T N N') :
    F + F' ∈ TT D T N N' := by
  obtain ⟨h1, m, hm, h2⟩ := hF
  obtain ⟨h1', m', hm', h2'⟩ := hF'
  refine ⟨h1.add h1', m * m', Nat.mul_pos hm hm', fun x hx => ?_⟩
  have e1 := h2 (m' • x) (AddSubgroup.nsmul_mem _ hx _)
  have e2 := h2' (m • x) (AddSubgroup.nsmul_mem _ hx _)
  rw [smul_smul] at e1 e2
  rw [mul_comm m' m] at e2
  rw [wd_add, e1, e2]

theorem tt_smul {T : Tor D} {N N' : ℕ} {F : VC D N N' → ℂ} (hF : F ∈ TT D T N N') (c : ℂ) :
    c • F ∈ TT D T N N' := by
  obtain ⟨h1, m, hm, h2⟩ := hF
  exact ⟨h1.const_smul c, m, hm, fun x hx => by rw [wd_smul, h2 x hx]⟩

theorem tt_sum {T : Tor D} {N N' : ℕ} {ι : Type*} (s : Finset ι) {F : ι → VC D N N' → ℂ}
    (hF : ∀ i ∈ s, F i ∈ TT D T N N') : ∑ i ∈ s, F i ∈ TT D T N N' := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using tt_zero T
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact tt_add (hF a (Finset.mem_insert_self a s)) (ih fun i hi => hF i (Finset.mem_insert_of_mem hi))

end GlobalTheory.FunObj.NormUniq
