module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
public import Formalism.LocalRingCardinality.DataExtra
public import Formalism.LocalRingCardinality.DataTies
public import Formalism.LocalToGlobal.Divisibility.CoefModLemmas
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHolRepOfIsTau
public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Init.Classical
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.GroupWithZero.Units.Lemmas
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Submodule.LinearMap
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Derivation
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.IsEmpty.Defs
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

noncomputable section

namespace GlobalTheory.JointHarm.FMul

open MvPolynomial Matrix Formalism.L2.DIV

section Lin

variable {σ : Type} [Fintype σ]

def lsub (M : Matrix σ σ ℂ) : MvPolynomial σ ℂ →ₐ[ℂ] MvPolynomial σ ℂ :=
  aeval fun v => ∑ w, C (M w v) * X w

theorem lsub_X (M : Matrix σ σ ℂ) (v : σ) : lsub M (X v) = ∑ w, C (M w v) * X w := aeval_X _ _



theorem constantCoeff_lsub (M : Matrix σ σ ℂ) (g : MvPolynomial σ ℂ) :
    constantCoeff (lsub M g) = constantCoeff g := by
  have : (constantCoeff : MvPolynomial σ ℂ →+* ℂ).comp (lsub M).toRingHom = constantCoeff := by
    apply MvPolynomial.ringHom_ext
    · intro a; simp
    · intro i; simp [lsub_X]
  exact congrArg (fun φ : MvPolynomial σ ℂ →+* ℂ => φ g) this

theorem pderiv_lsub [DecidableEq σ] (M : Matrix σ σ ℂ) (s : σ) (g : MvPolynomial σ ℂ) :
    pderiv s (lsub M g) = ∑ w, C (M s w) * lsub M (pderiv w g) := by
  induction g using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp only [map_add (f := _), hp, hq, mul_add, Finset.sum_add_distrib]
  | mul_X p k hp =>
    have hX : pderiv s (lsub M (X k)) = C (M s k) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [lsub_X, map_sum, Finset.sum_eq_single s]
      · simp [pderiv_X]
      · intro b _ hb
        rw [Derivation.leibniz, pderiv_C, pderiv_X_of_ne hb]
        simp
      · simp
    rw [map_mul, Derivation.leibniz, hX, hp, smul_eq_mul, smul_eq_mul]
    simp_rw [Derivation.leibniz, smul_eq_mul, map_add (f := _), map_mul, mul_add, Finset.sum_add_distrib]
    congr 1
    · rw [Finset.sum_eq_single k]
      · rw [pderiv_X_self, map_one]; ring
      · intro b _ hb
        rw [pderiv_X_of_ne hb.symm]
        simp
      · simp
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring

theorem fockL_lsub_adj (M : Matrix σ σ ℂ) (F F' : MvPolynomial σ ℂ) :
    fockL (lsub M F) F' = fockL F (lsub Mᴴ F') := by
  classical
  induction F using MvPolynomial.induction_on generalizing F' with
  | C a => rw [algHom_C, algebraMap_eq, fockL_C_left, fockL_C_left, constantCoeff_lsub]
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), map_add (f := _), LinearMap.add_apply, LinearMap.add_apply, hp, hq]
  | mul_X p v hp =>
    have e1 : lsub M (p * X v) = ∑ w, M w v • (X w * lsub M p) := by
      rw [map_mul, lsub_X, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [smul_eq_C_mul]; ring
    set_option synthInstance.maxHeartbeats 100000 in
      rw [e1, map_sum, LinearMap.sum_apply]
    simp_rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, fockL_X_pderiv, hp]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [mul_comm p, fockL_X_pderiv, pderiv_lsub, map_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← smul_eq_C_mul, map_smul, Matrix.conjTranspose_apply, starRingEnd_apply]

end Lin

section Blocks

variable {m n : ℕ}











variable {ι : Type} [DecidableEq ι]





end Blocks

end GlobalTheory.JointHarm.FMul

namespace GlobalTheory.JointHarm

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.JointHarm
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

section

variable {D : D7} {m n : ℕ}





end


end GlobalTheory.JointHarm

end
