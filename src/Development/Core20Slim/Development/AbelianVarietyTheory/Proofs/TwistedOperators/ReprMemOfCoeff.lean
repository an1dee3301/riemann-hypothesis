module

public import Mathlib
public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkMapInitMinor
public import Formalism.LocalRingCardinality.DataCoeff
public import Init.Core
public import Init.Data.Function
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Ker
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Module.Submodule.LinearMap
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Finsupp.SMul
public import Mathlib.Data.Finsupp.SMulWithZero
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Int.Cast.Lemmas
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.RingTheory.PicardGroup

@[expose] public section

noncomputable section

open Formalism.L2.DIV MvPolynomial

namespace GlobalTheory.RowRat

theorem exists_proj (K' : Subfield ℂ) : ∃ φ : ℂ →ₗ[K'] ℂ, (∀ x : K', φ x = x) ∧ ∀ x, φ x ∈ K' := by
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap K' ℂ)
    (LinearMap.ker_eq_bot.2 (FaithfulSMul.algebraMap_injective K' ℂ))
  refine ⟨(Algebra.linearMap K' ℂ).comp g, fun x => ?_, fun x => (g x).2⟩
  have h := congrArg (fun f => f x) hg
  simp only [LinearMap.comp_apply, LinearMap.id_apply] at h
  show algebraMap K' ℂ (g (Algebra.linearMap K' ℂ x)) = algebraMap K' ℂ x
  rw [h]

theorem val_eq_sum_repr {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → Formalism.BasicNotions.DomWeight n) (v : VV ℂ lam) :
    v.1 = ∑ a, (bVV ℂ lam).repr v a • bVVfun ℂ lam a := by
  conv_lhs => rw [← (bVV ℂ lam).sum_repr v]
  rw [Submodule.coe_sum]
  simp only [Submodule.coe_smul, bVV_coe]

theorem coeff_mem_of_repr {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → Formalism.BasicNotions.DomWeight n) {L : Type} [Field L]
    (κ : L →+* ℂ) (v : VV ℂ lam) (h : ∀ a, (bVV ℂ lam).repr v a ∈ Set.range κ) (m : ι × Fin n × Fin n →₀ ℕ) :
    AddMonoidAlgebra.coeff v.1 m ∈ Set.range κ := by
  rw [val_eq_sum_repr, coeff_sum, ← RingHom.coe_fieldRange]
  refine Subfield.sum_mem _ fun a _ => ?_
  obtain ⟨P, hP⟩ := bVVfun_int ℂ lam a
  rw [coeff_smul, hP, coeff_map, smul_eq_mul]
  obtain ⟨x, hx⟩ := h a
  exact ⟨x * P.coeff m, by simp [hx]⟩

end GlobalTheory.RowRat

namespace GlobalTheory.RowRat
open Formalism.L2.DIV MvPolynomial

theorem repr_mem_of_coeff {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → Formalism.BasicNotions.DomWeight n) {L : Type} [Field L]
    (κ : L →+* ℂ) (v : VV ℂ lam) (h : ∀ m, AddMonoidAlgebra.coeff v.1 m ∈ Set.range κ) (a : VVIdx lam) :
    (bVV ℂ lam).repr v a ∈ Set.range κ := by
  set K' := κ.fieldRange
  obtain ⟨φ, hφ1, hφ2⟩ := exists_proj K'
  set c := fun a => (bVV ℂ lam).repr v a
  have hK : ∀ a m, AddMonoidAlgebra.coeff (bVVfun ℂ lam a) m ∈ K' := fun a m => by
    obtain ⟨P, hP⟩ := bVVfun_int ℂ lam a
    rw [hP, coeff_map]
    exact ⟨((AddMonoidAlgebra.coeff P m : ℤ) : L), by simp⟩
  have key : ∑ b, (c b - φ (c b)) • bVVfun ℂ lam b = 0 := by
    ext m
    have e1 : AddMonoidAlgebra.coeff v.1 m = ∑ b, c b * AddMonoidAlgebra.coeff (bVVfun ℂ lam b) m := by
      rw [val_eq_sum_repr, coeff_sum]; simp [c]
    have e2 : φ (AddMonoidAlgebra.coeff v.1 m) = AddMonoidAlgebra.coeff v.1 m := hφ1 ⟨_, RingHom.mem_fieldRange.2 (h m)⟩
    have e3 : φ (AddMonoidAlgebra.coeff v.1 m) = ∑ b, φ (c b) * AddMonoidAlgebra.coeff (bVVfun ℂ lam b) m := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [e1, map_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      have : c b * AddMonoidAlgebra.coeff (bVVfun ℂ lam b) m = (⟨_, hK b m⟩ : K') • c b := by
        rw [Subfield.smul_def, smul_eq_mul, mul_comm]
      rw [this, map_smul, Subfield.smul_def, smul_eq_mul, mul_comm]
    rw [coeff_sum, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
    simp only [coeff_smul, smul_eq_mul, sub_mul, Finset.sum_sub_distrib]
    rw [← e1, ← e3, e2, sub_self]
  have hz := Fintype.linearIndependent_iff.1 (bVVfun_spec ℂ lam).1 _ key a
  rw [sub_eq_zero] at hz
  have hc : c a ∈ K' := by rw [hz]; exact hφ2 _
  exact RingHom.mem_fieldRange.1 hc

end GlobalTheory.RowRat

namespace GlobalTheory.RowRat
open Formalism.L2.DIV MvPolynomial

theorem coeff_map_mem {ι : Type} [Fintype ι] {n n' : ℕ} {σ : ι → Formalism.BasicNotions.DomWeight n} {σ' : ι → Formalism.BasicNotions.DomWeight n'} {L : Type} [Field L] (κ : L →+* ℂ)
    (f : VV ℂ σ →ₗ[ℂ] VV ℂ σ') (hf : ∀ a b, (bVV ℂ σ').repr (f (bVV ℂ σ b)) a ∈ Set.range κ) (v : VV ℂ σ)
    (hv : ∀ m, AddMonoidAlgebra.coeff v.1 m ∈ Set.range κ) (m : ι × Fin n' × Fin n' →₀ ℕ) :
    AddMonoidAlgebra.coeff (f v).1 m ∈ Set.range κ := by
  refine coeff_mem_of_repr σ' κ _ (fun a => ?_) m
  have e : f v = ∑ b, (bVV ℂ σ).repr v b • f (bVV ℂ σ b) := by
    conv_lhs => rw [← (bVV ℂ σ).sum_repr v]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul]
  rw [e]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul]
  rw [← RingHom.coe_fieldRange]
  refine Subfield.sum_mem _ fun b _ => ?_
  exact Subfield.mul_mem _ (RingHom.mem_fieldRange.2 (repr_mem_of_coeff σ κ v hv b)) (RingHom.mem_fieldRange.2 (hf a b))

end GlobalTheory.RowRat

end
