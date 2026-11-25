module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEval
public import Init.Classical
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.PropLemmas
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Derivation
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Empty
public import Mathlib.Data.Finset.Erase
public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Prod.Basic
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Multilinear.Basic
public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
public import Mathlib.Logic.Function.Basic
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic

@[expose] public section

open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

noncomputable section
namespace GlobalTheory.CCRFock

theorem pderiv_rename_prodMk_of_ne {W Λ : Type} {v w : W} (h : v ≠ w) (l : Λ) (r : MvPolynomial Λ ℂ) :
    MvPolynomial.pderiv (w, l) (MvPolynomial.rename (Prod.mk v) r) = 0 := by
  induction r using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
    rw [map_mul, MvPolynomial.rename_X, Derivation.leibniz, hp, MvPolynomial.pderiv_X_of_ne]
    · simp
    · intro e; exact h (congrArg Prod.fst e)

theorem pderiv_prod_rename_of_notMem {W Λ : Type} {w : W} (l : Λ) (q : W → MvPolynomial Λ ℂ) (s : Finset W)
    (hs : w ∉ s) :
    MvPolynomial.pderiv (w, l) (∏ v ∈ s, MvPolynomial.rename (Prod.mk v) (q v)) = 0 := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.mem_insert, not_or] at hs
    rw [Finset.prod_insert ha, Derivation.leibniz, ih hs.2,
      pderiv_rename_prodMk_of_ne (fun e => hs.1 e.symm)]
    simp

theorem polMap_comp_atPl_pderiv (W Λ : Type) [Fintype W] [DecidableEq W] (w : W) (l : Λ) :
    GlobalTheory.CCRFock.polMap W Λ ∘ₗ GlobalTheory.RealLift.atPl (V := fun _ : W => MvPolynomial Λ ℂ) w
                 (MvPolynomial.pderiv l).toLinearMap =
      (MvPolynomial.pderiv (w, l)).toLinearMap ∘ₗ GlobalTheory.CCRFock.polMap W Λ := by
  apply PiTensorProduct.ext
  ext1 q
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, polMap, atPl, PiTensorProduct.map_tprod,
    PiTensorProduct.lift.tprod, MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply,
    AlgHom.toLinearMap_apply]
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ w),
    ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ w)]
  have h1 : ∏ i ∈ Finset.univ.erase w, MvPolynomial.rename (Prod.mk i)
      ((Function.update (fun _ : W => (LinearMap.id : MvPolynomial Λ ℂ →ₗ[ℂ] MvPolynomial Λ ℂ)) w
        (MvPolynomial.pderiv l).toLinearMap i) (q i)) =
      ∏ i ∈ Finset.univ.erase w, MvPolynomial.rename (Prod.mk i) (q i) :=
    Finset.prod_congr rfl fun i hi => by
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hi), LinearMap.id_apply]
  rw [h1, Function.update_self, Derivation.coeFn_coe, Derivation.coeFn_coe, Derivation.leibniz,
    pderiv_prod_rename_of_notMem l q _ (Finset.notMem_erase w _),
    MvPolynomial.pderiv_rename (Prod.mk_right_injective w) l (q w)]
  simp [mul_comm]

end GlobalTheory.CCRFock
