module

public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.InvGroup
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.NullSec
public import Init.ByCases
public import Init.Core
public import Init.Data.Bool
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
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
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.GroupWithZero.Units.Lemmas
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.IsEmpty.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Basis
public import Mathlib.Data.NNRat.Defs
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Rat.Init
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Tactic.Ring.RingNF

@[expose] public section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open MvPolynomial

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.IInvH

variable {D : D7} {m n : ℕ}

def xyC (Z : Matrix (Fin m) (Fin m) ℂ) (a : Fin m) (i : Fin n) (b : Bool) : PX m n :=
  ∑ c, C (Z a c) * MvPolynomial.X (c, i, b)

def vfC (c : ℝ) (Zh Za : Matrix (Fin m) (Fin m) ℂ) (P : PX m n) : PX m n :=
  ∑ a, ∑ i, (xyC Zh a i false * pderiv (a, i, false) P + xyC Za a i true * pderiv (a, i, true) P -
    C (c : ℂ) * (xyC Zh a i false * MvPolynomial.X (a, i, true) + xyC Za a i true * MvPolynomial.X (a, i, false)) * P)

theorem vfX_eq (c : ℝ) (Z : Matrix (Fin m) (Fin m) ℂ) (P : PX m n) : vfX c Z P = vfC c Z (Z.map star) P := by
  have h1 : ∀ a (i : Fin n), xyP Z a i false = xyC Z a i false := fun a i => by simp [xyP, xyC]
  have h2 : ∀ a (i : Fin n), xyP Z a i true = xyC (Z.map star) a i true := fun a i => by simp [xyP, xyC, Matrix.map_apply]
  simp only [vfX, vfC, h1, h2]

theorem xyC_add_smul (Z Z' : Matrix (Fin m) (Fin m) ℂ) (r : ℂ) (a : Fin m) (i : Fin n) (b : Bool) :
    xyC (Z + r • Z') a i b = xyC Z a i b + C r * xyC Z' a i b := by
  simp only [xyC, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add (f := _), map_mul, add_mul, Finset.sum_add_distrib,
    Finset.mul_sum, mul_assoc]

theorem vfC_lin (c : ℝ) (Zh Za Zh' Za' : Matrix (Fin m) (Fin m) ℂ) (r : ℂ) (P : PX m n) :
    vfC c Zh Za P + r • vfC c Zh' Za' P = vfC c (Zh + r • Zh') (Za + r • Za') P := by
  simp only [vfC, xyC_add_smul, smul_eq_C_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ => ?_
  ring

theorem xyC_single (a b a' : Fin m) (r : ℂ) (i : Fin n) (β : Bool) :
    xyC (r • Matrix.single a b (1 : ℂ)) a' i β = if a' = a then C r * MvPolynomial.X (b, i, β) else 0 := by
  by_cases h : a' = a
  · subst h
    simp only [xyC, Matrix.smul_apply, Matrix.single_apply, true_and, smul_eq_mul, mul_ite, mul_one,
      mul_zero, if_true]
    rw [Finset.sum_eq_single b]
    · simp
    · intro x _ hx
      simp [Ne.symm hx]
    · simp
  · simp [xyC, Matrix.single_apply, h, Ne.symm h]

theorem sgn_star (ε : Fin m → Bool) (a : Fin m) : star (sgn ε a) = sgn ε a := by
  unfold sgn; split_ifs <;> simp

theorem zRe_add_zIm (ε : Fin m → Bool) (a b : Fin m) :
    zRe ε a b + Complex.I • zIm ε a b = (1 : ℂ) • Matrix.single a b (1 : ℂ) := by
  ext i j
  simp only [zRe, zIm, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
  ring_nf
  rw [Complex.I_sq]
  ring

theorem zRe_add_zIm_star (ε : Fin m → Bool) (a b : Fin m) :
    (zRe ε a b).map star + Complex.I • (zIm ε a b).map star = (-(sgn ε a * sgn ε b)) • Matrix.single b a (1 : ℂ) := by
  have hs : (starRingEnd ℂ) (sgn ε a) = sgn ε a := sgn_star ε a
  have ht : (starRingEnd ℂ) (sgn ε b) = sgn ε b := sgn_star ε b
  have h2 : (starRingEnd ℂ) (2 : ℂ) = 2 := map_ofNat _ 2
  ext i j
  simp only [zRe, zIm, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.map_apply,
    smul_eq_mul, Matrix.neg_apply, Matrix.single_apply, Complex.star_def]
  split_ifs <;> simp [map_add (f := _), map_mul, map_neg, map_sub, hs, ht, h2, Complex.conj_I] <;> ring_nf <;>
    simp [Complex.I_sq] <;> ring

theorem hOp_eq (ε : Fin m → Bool) (c : ℝ) (a b : Fin m) (P : PX m n) :
    hOp ε c a b P = vfX c (zRe ε a b) P + Complex.I • vfX c (zIm ε a b) P := by
  rw [vfX_eq, vfX_eq, vfC_lin, zRe_add_zIm, zRe_add_zIm_star]
  unfold vfC hOp
  simp only [xyC_single]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [ite_mul, zero_mul, mul_ite, mul_zero, add_mul, mul_add]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [map_neg, map_one, map_mul, map_sub]
  ring

end PositivityTheory.Rg.Sw.Glob.IInvH
