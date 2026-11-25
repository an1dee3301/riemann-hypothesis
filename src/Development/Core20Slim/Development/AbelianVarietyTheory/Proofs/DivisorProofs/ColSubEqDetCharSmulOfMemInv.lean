module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdMinorsMemInv
public import Formalism.LocalToGlobal.Columns.PolyFn
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteBottomRowTransportContragredient
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.MvPolynomial.Monad
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic

@[expose] public section

open Classical

noncomputable section

namespace GlobalTheory.MinorFrame

open MvPolynomial

variable {ι : Type} [Fintype ι]

def genColSub (d a : ℕ) : Pol ι d a →ₐ[ℂ] MvPolynomial (Var ι d a) (MvPolynomial (ι × Fin a × Fin a) ℂ) :=
  aeval fun y => ∑ j' : Fin a, C (X (y.1, j', y.2.2)) * X (y.1, y.2.1, j')

omit [Fintype ι] in
theorem map_eval_genColSub {d a : ℕ} (g : ι → Matrix (Fin a) (Fin a) ℂ) (P : Pol ι d a) :
    map (eval fun x : ι × Fin a × Fin a => g x.1 x.2.1 x.2.2) (genColSub d a P) = colSub g P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [genColSub, colSub, algebraMap_eq]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p y hp =>
    simp only [map_mul, hp]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [genColSub, colSub, map_sum]

def genDetChar (a : ℕ) (n : ι → ℕ) : MvPolynomial (ι × Fin a × Fin a) ℂ :=
  ∏ τ, (Matrix.of fun i j => (X (τ, i, j) : MvPolynomial (ι × Fin a × Fin a) ℂ)).det ^ n τ

theorem eval_genDetChar {a : ℕ} (n : ι → ℕ) (g : ι → Matrix (Fin a) (Fin a) ℂ) :
    eval (fun x : ι × Fin a × Fin a => g x.1 x.2.1 x.2.2) (genDetChar a n) = detChar n g := by
  rw [genDetChar, map_prod, detChar]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [map_pow, RingHom.map_det]
  congr 2
  ext i j
  simp

theorem colSub_eq_detChar_smul_of_mem_inv {a d : ℕ} (n : ι → ℕ) (P : Pol ι d a) (hP : P ∈ inv a d n)
    (g : ι → Matrix (Fin a) (Fin a) ℂ) : colSub g P = detChar n g • P := by
  set D : MvPolynomial (Var ι d a) (MvPolynomial (ι × Fin a × Fin a) ℂ) :=
    genColSub d a P - C (genDetChar a n) * map C P with hDdef
  have hD : ∀ g : ι → Matrix (Fin a) (Fin a) ℂ,
      map (eval fun x : ι × Fin a × Fin a => g x.1 x.2.1 x.2.2) D = colSub g P - detChar n g • P := by
    intro g
    rw [hDdef, map_sub, map_mul, map_C, map_eval_genColSub, eval_genDetChar, map_map, smul_eq_C_mul]
    congr 2
    have : (eval fun x : ι × Fin a × Fin a => g x.1 x.2.1 x.2.2).comp (C : ℂ →+* MvPolynomial (ι × Fin a × Fin a) ℂ) =
        RingHom.id ℂ := by ext; simp
    rw [this, map_id]
  have hD0 : D = 0 := by
    refine MvPolynomial.ext _ _ fun m => ?_
    simp only [AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
    refine Formalism.L2.Col.eq_zero_of_forall_unitary (ι := ι) (n := a) (fun _ => 1) (fun _ => by simp) _ fun u hu => ?_
    simp only [Matrix.one_mul]
    rw [← coeff_map, hD u]
    have hu' : ∀ τ, u τ ∈ Matrix.unitaryGroup (Fin a) ℂ := fun τ =>
      Matrix.mem_unitaryGroup_iff'.mpr (by simpa [Matrix.star_eq_conjTranspose] using hu τ)
    have := hP (fun τ => ⟨u τ, hu' τ⟩)
    simp only at this
    simp only [this, sub_self, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
  have := hD g
  rw [hD0, _root_.map_zero] at this
  exact (sub_eq_zero.mp this.symm)

end GlobalTheory.MinorFrame
