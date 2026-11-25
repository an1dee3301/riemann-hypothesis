module

public import Mathlib
public import Development.Core20Slim.Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.AlmostGoodOf
public import Development.Core20Slim.Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.BasisSet
public import Development.Core20Slim.Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.TraceDual
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import Init.Classical
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.BigOperators
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Basic
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Finset.Lattice.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Finsupp.SMul
public import Mathlib.Data.Finsupp.SMulWithZero
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Discriminant
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Free
public import Mathlib.RingTheory.Valuation.ValuationSubring

@[expose] public section

noncomputable section

namespace GlobalTheory.CompanionTheory.RvRingPf

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain PositivityTheory.PfSWUS.Loc PositivityTheory.SiegelWeilFormula.Gen PositivityTheory.SiegelWeilFormula.Gunr
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem repr_one_tmul {d : ℕ} (bs : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (e : E) (k : Fin d) :
    (Algebra.TensorProduct.basis (Fv F v) bs).repr ((1 : Fv F v) ⊗ₜ[F] e) k =
      algebraMap F (Fv F v) (bs.repr e k) := by
  rw [Algebra.TensorProduct.basis_repr_tmul]
  simp

theorem struct_int {σ : E →ₐ[F] E} {d : ℕ} {bs : Module.Basis (Fin d) F E} {v : HeightOneSpectrum (𝓞 F)}
    (h : IntAt v (basisSet σ bs)) (i j k : Fin d) :
    algebraMap F (Fv F v) (bs.repr (bs i * bs j) k) ∈ v.adicCompletionIntegers F := by
  refine h _ ?_
  classical
  unfold basisSet
  refine Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ ?_))
  exact Finset.mem_image.2 ⟨(i, j, k), Finset.mem_univ _, rfl⟩

theorem one_int {σ : E →ₐ[F] E} {d : ℕ} {bs : Module.Basis (Fin d) F E} {v : HeightOneSpectrum (𝓞 F)}
    (h : IntAt v (basisSet σ bs)) (k : Fin d) :
    algebraMap F (Fv F v) (bs.repr 1 k) ∈ v.adicCompletionIntegers F := by
  refine h _ ?_
  classical
  unfold basisSet
  refine Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ ?_))
  exact Finset.mem_image.2 ⟨k, Finset.mem_univ _, rfl⟩

theorem sig_int {σ : E →ₐ[F] E} {d : ℕ} {bs : Module.Basis (Fin d) F E} {v : HeightOneSpectrum (𝓞 F)}
    (h : IntAt v (basisSet σ bs)) (i k : Fin d) :
    algebraMap F (Fv F v) (bs.repr (σ (bs i)) k) ∈ v.adicCompletionIntegers F := by
  refine h _ ?_
  classical
  unfold basisSet
  refine Finset.mem_union_left _ (Finset.mem_union_right _ ?_)
  exact Finset.mem_image.2 ⟨(i, k), Finset.mem_univ _, rfl⟩

theorem repr_mul {d : ℕ} (bs : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F))
    (x y : Fv F v ⊗[F] E) (k : Fin d) :
    (Algebra.TensorProduct.basis (Fv F v) bs).repr (x * y) k =
      ∑ i, ∑ j, ((Algebra.TensorProduct.basis (Fv F v) bs).repr x i *
        (Algebra.TensorProduct.basis (Fv F v) bs).repr y j) *
          algebraMap F (Fv F v) (bs.repr (bs i * bs j) k) := by
  set bK := Algebra.TensorProduct.basis (Fv F v) bs with hbK
  have e : x * y = ∑ i, ∑ j, (bK.repr x i * bK.repr y j) • ((1 : Fv F v) ⊗ₜ[F] (bs i * bs j)) := by
    conv_lhs => rw [← bK.sum_repr x, ← bK.sum_repr y]
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [smul_mul_smul_comm, hbK, Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.basis_apply,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← bK.coord_apply, e, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, bK.coord_apply, hbK, repr_one_tmul, smul_eq_mul]

theorem repr_sig (σ : E →ₐ[F] E) {d : ℕ} (bs : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F))
    (x : Fv F v ⊗[F] E) (k : Fin d) :
    (Algebra.TensorProduct.basis (Fv F v) bs).repr (sigR (Fv F v) σ x) k =
      ∑ i, (Algebra.TensorProduct.basis (Fv F v) bs).repr x i *
        algebraMap F (Fv F v) (bs.repr (σ (bs i)) k) := by
  set bK := Algebra.TensorProduct.basis (Fv F v) bs with hbK
  have e : sigR (Fv F v) σ x = ∑ i, bK.repr x i • ((1 : Fv F v) ⊗ₜ[F] σ (bs i)) := by
    conv_lhs => rw [← bK.sum_repr x]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hbK, Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one,
      TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    simp [sigR]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← bK.coord_apply, e, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, bK.coord_apply, hbK, repr_one_tmul, smul_eq_mul]

def ringOf {σ : E →ₐ[F] E} {d : ℕ} {bs : Module.Basis (Fin d) F E} {v : HeightOneSpectrum (𝓞 F)}
    (h : IntAt v (basisSet σ bs)) : Subring (Fv F v ⊗[F] E) where
  carrier := Rv bs v
  mul_mem' := by
    intro x y hx hy k
    rw [repr_mul]
    exact sum_mem fun i _ => sum_mem fun j _ => mul_mem (mul_mem (hx i) (hy j)) (struct_int h i j k)
  one_mem' := by
    intro k
    rw [Algebra.TensorProduct.one_def, repr_one_tmul]
    exact one_int h k
  add_mem' := by
    intro x y hx hy k
    rw [map_add (f := _), Finsupp.add_apply]
    exact add_mem (hx k) (hy k)
  zero_mem' := by
    intro k
    rw [map_zero, Finsupp.zero_apply]
    exact zero_mem _
  neg_mem' := by
    intro x hx k
    rw [map_neg, Finsupp.neg_apply]
    exact neg_mem (hx k)

theorem sigR_mem {σ : E →ₐ[F] E} {d : ℕ} {bs : Module.Basis (Fin d) F E} {v : HeightOneSpectrum (𝓞 F)}
    (h : IntAt v (basisSet σ bs)) (x : Fv F v ⊗[F] E) (hx : x ∈ ringOf h) :
    sigR (Fv F v) σ x ∈ ringOf h := by
  intro k
  rw [repr_sig]
  exact sum_mem fun i _ => mul_mem (hx i) (sig_int h i k)

theorem rvRing : PositivityTheory.SiegelWeilFormula.Gunr.RvRing := by
  intro F E _ _ _ _ _ σ d bs v h
  exact ⟨ringOf h, (sigR (Fv F v) σ).restrict (ringOf h) (ringOf h) (sigR_mem h), rfl, fun x => rfl⟩

end GlobalTheory.CompanionTheory.RvRingPf

end
