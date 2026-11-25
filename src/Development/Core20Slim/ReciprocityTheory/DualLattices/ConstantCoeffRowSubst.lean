module

public import Development.Core20Slim.ReciprocityTheory.DualLattices.FischerSmulRight
public import Init.Classical
public import Init.Core
public import Init.Data.Zero
public import Init.Ext
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
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
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Derivation
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.MvPolynomial.Monad
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Basic
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Development.Core20Slim.ReciprocityTheory.DualLattices.FischerAdjointStatement

@[expose] public section

noncomputable section

open MvPolynomial Matrix Finset

open scoped Classical

namespace ReciprocityTheory.PGsh

variable {ν : ℕ} {ι : Type*}

theorem rowSubst_X (g : Matrix (Fin ν) (Fin ν) ℂ) (p : Fin ν × ι) :
    rowSubst g (X p) = ∑ l, C (g l p.1) * X (l, p.2) := by
  simp [rowSubst]

theorem rowSubst_C (g : Matrix (Fin ν) (Fin ν) ℂ) (c : ℂ) :
    rowSubst g (C c : MvPolynomial (Fin ν × ι) ℂ) = C c := by
  simp [rowSubst]

theorem constantCoeff_rowSubst (h : Matrix (Fin ν) (Fin ν) ℂ) (Q : MvPolynomial (Fin ν × ι) ℂ) :
    constantCoeff (rowSubst h Q) = constantCoeff Q := by
  induction Q using MvPolynomial.induction_on with
  | C a => rw [rowSubst_C]
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), map_add (f := _), hp, hq]
  | mul_X p n hp => simp [map_mul, hp, rowSubst_X]

theorem coeff_zero_rowSubst (h : Matrix (Fin ν) (Fin ν) ℂ) (Q : MvPolynomial (Fin ν × ι) ℂ) :
    AddMonoidAlgebra.coeff (rowSubst h Q) 0 = AddMonoidAlgebra.coeff Q 0 := by
  exact constantCoeff_rowSubst h Q

theorem pderiv_rowSubst_X (h : Matrix (Fin ν) (Fin ν) ℂ) (k : Fin ν) (a : ι) (s : Fin ν × ι) :
    pderiv (k, a) (rowSubst h (X s : MvPolynomial (Fin ν × ι) ℂ)) =
      if s.2 = a then C (h k s.1) else 0 := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [rowSubst_X, map_sum]
  by_cases hs : s.2 = a
  · simp [pderiv_C_mul, pderiv_X, Pi.single_apply, hs]
  · simp [pderiv_C_mul, pderiv_X, Pi.single_apply, hs]

theorem pderiv_rowSubst (h : Matrix (Fin ν) (Fin ν) ℂ) (k : Fin ν) (a : ι)
    (Q : MvPolynomial (Fin ν × ι) ℂ) :
    pderiv (k, a) (rowSubst h Q) = ∑ m, C (h k m) * rowSubst h (pderiv (m, a) Q) := by
  induction Q using MvPolynomial.induction_on with
  | C c => simp [rowSubst_C]
  | add p q hp hq => simp only [map_add (f := _), hp, hq, mul_add, Finset.sum_add_distrib]
  | mul_X p n hp =>
    have e1 : ∀ m, rowSubst h (pderiv (m, a) (X n : MvPolynomial (Fin ν × ι) ℂ)) =
        if n = (m, a) then 1 else 0 := by
      intro m
      rw [pderiv_X, Pi.single_apply]
      split_ifs <;> simp
    have e2 : ∑ m, C (h k m) * (rowSubst h p * (if n = (m, a) then 1 else 0)) =
        rowSubst h p * (if n.2 = a then C (h k n.1) else 0) := by
      by_cases hn : n.2 = a
      · rw [if_pos hn, Finset.sum_eq_single n.1]
        · rw [if_pos (show n = (n.1, a) from Prod.ext rfl hn)]
          ring
        · intro m _ hm
          rw [if_neg (fun h' => hm (congrArg Prod.fst h').symm)]
          ring
        · intro h'
          exact absurd (Finset.mem_univ _) h'
      · rw [if_neg hn, mul_zero]
        refine Finset.sum_eq_zero (fun m _ => ?_)
        rw [if_neg (fun h' => hn (congrArg Prod.snd h'))]
        ring
    rw [map_mul, Derivation.leibniz, hp, pderiv_rowSubst_X, smul_eq_mul, smul_eq_mul, ← e2,
      Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [Derivation.leibniz, map_add (f := _), smul_eq_mul, smul_eq_mul, map_mul, map_mul, e1]
    ring

theorem fischer_rowSubst (g : Matrix (Fin ν) (Fin ν) ℂ) (P Q : MvPolynomial (Fin ν × ι) ℂ) :
    fischer (rowSubst g P) Q = fischer P (rowSubst gᴴ Q) := by
  induction P using MvPolynomial.induction_on generalizing Q with
  | C c =>
    rw [rowSubst_C, fischer_C_left, fischer_C_left, coeff_zero_rowSubst]
  | add p q hp hq =>
    rw [map_add (f := _), fischer_add_left, fischer_add_left, hp, hq]
  | mul_X p n hp =>
    rcases n with ⟨k, a⟩
    rw [map_mul, rowSubst_X, Finset.mul_sum, fischer_sum_left, fischer_mul_X, pderiv_rowSubst,
      fischer_sum_right]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [mul_left_comm, MvPolynomial.C_mul', fischer_smul_left, fischer_mul_X, hp, MvPolynomial.C_mul',
      fischer_smul_right]
    simp [Matrix.conjTranspose_apply]

end ReciprocityTheory.PGsh
