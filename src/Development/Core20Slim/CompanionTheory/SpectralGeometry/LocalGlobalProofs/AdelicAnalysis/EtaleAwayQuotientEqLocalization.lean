module

public import Mathlib
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Basic
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Finsupp.SMul
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.FieldTheory.Perfect
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Nondegenerate
public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.LinearAlgebra.SesquilinearForm.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Free
public import Mathlib.RingTheory.Trace.Basic
public import Mathlib.RingTheory.Trace.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.TraceFormGram

open HeckeCharacterZeroLocus.SiegelWeilU
open scoped TensorProduct Matrix

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem trace_tmul [FiniteDimensional F E] (R : Type) [CommRing R] [Algebra F R] (a : R) (e : E) :
    Algebra.trace R (R ⊗[F] E) (a ⊗ₜ[F] e) = a * algebraMap F R (Algebra.trace F E e) := by
  have h1 : Algebra.trace R (R ⊗[F] E) ((1 : R) ⊗ₜ[F] e) = algebraMap F R (Algebra.trace F E e) := by
    rw [Algebra.trace_apply, Algebra.trace_apply, ← LinearMap.trace_baseChange]
    congr 1
    ext y
    simp [Algebra.TensorProduct.tmul_mul_tmul, LinearMap.baseChange_tmul]
  have h2 : a ⊗ₜ[F] e = a • ((1 : R) ⊗ₜ[F] e) := by
    simp [TensorProduct.smul_tmul']
  rw [h2, map_smul, h1, smul_eq_mul]

theorem expand {d : ℕ} (b : Module.Basis (Fin d) F E) (R : Type) [CommRing R] [Algebra F R]
    (u : R ⊗[F] E) :
    u = ∑ k, ((Algebra.TensorProduct.basis R b).repr u k) ⊗ₜ[F] b k := by
  conv_lhs => rw [← (Algebra.TensorProduct.basis R b).sum_repr u]
  simp [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul']

def trGram (σ : E →ₐ[F] E) {M d : ℕ} (J : Matrix (Fin M) (Fin M) E) (b : Module.Basis (Fin d) F E) :
    Matrix (Fin M × Fin d) (Fin M × Fin d) F :=
  fun p q => Algebra.trace F E (σ (b p.2) * J p.1 q.1 * b q.2)

theorem trace_entry [FiniteDimensional F E] (σ : E →ₐ[F] E) {d : ℕ} (b : Module.Basis (Fin d) F E)
    (R : Type) [CommRing R] [Algebra F R] (u v : R ⊗[F] E) (e : E) :
    Algebra.trace R (R ⊗[F] E) (sigR R σ u * ((1 : R) ⊗ₜ[F] e) * v) =
      ∑ k, ∑ l, (Algebra.TensorProduct.basis R b).repr u k *
        (algebraMap F R (Algebra.trace F E (σ (b k) * e * b l)) *
          (Algebra.TensorProduct.basis R b).repr v l) := by
  conv_lhs => rw [expand b R u, expand b R v]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  have : sigR R σ (((Algebra.TensorProduct.basis R b).repr u k) ⊗ₜ[F] b k) =
      ((Algebra.TensorProduct.basis R b).repr u k) ⊗ₜ[F] σ (b k) := by
    simp [sigR]
  rw [this, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, trace_tmul]
  simp only [mul_one]
  ring

section CM

variable [NumberField F] [NumberField E]

theorem sig_sig {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2, h.2.2.2, star_star]

theorem trace_sig {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (x : E) :
    Algebra.trace F E (σ x) = Algebra.trace F E x :=
  Algebra.trace_eq_of_algEquiv
    (AlgEquiv.ofAlgHom σ σ (AlgHom.ext (sig_sig h)) (AlgHom.ext (sig_sig h))) x

theorem trGram_isSymm {σ : E →ₐ[F] E} (h : IsCMExt F E σ) {M d : ℕ}
    {J : Matrix (Fin M) (Fin M) E} (hJ : IsHermND σ J) (b : Module.Basis (Fin d) F E) :
    (trGram σ J b).IsSymm := by
  ext ⟨i, k⟩ ⟨j, l⟩
  simp only [Matrix.transpose_apply, trGram]
  rw [← trace_sig h (σ (b l) * J j i * b k)]
  simp only [map_mul, sig_sig h, hJ.1]
  congr 1
  ring

theorem trGram_det_ne_zero {σ : E →ₐ[F] E} (h : IsCMExt F E σ) {M d : ℕ}
    {J : Matrix (Fin M) (Fin M) E} (hJ : IsHermND σ J) (b : Module.Basis (Fin d) F E) :
    (trGram σ J b).det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv, hBv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  set y : Fin M → E := fun j => ∑ l, v (j, l) • b l with hy
  have key : ∀ i k, Algebra.trace F E (σ (b k) * (J *ᵥ y) i) = 0 := by
    intro i k
    have h0 := congrFun hBv (i, k)
    simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, trGram, Pi.zero_apply] at h0
    rw [← h0]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mulVec, dotProduct, hy, Finset.mul_sum, map_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
    rw [mul_smul_comm, mul_smul_comm, map_smul, smul_eq_mul, mul_comm, mul_assoc]
  have key2 : ∀ i (e : E), Algebra.trace F E (e * (J *ᵥ y) i) = 0 := by
    intro i e
    have he : e = ∑ k, (b.repr (σ e) k) • σ (b k) := by
      have h3 := congrArg σ (b.sum_repr (σ e))
      set_option synthInstance.maxHeartbeats 100000 in
        rw [sig_sig h, map_sum] at h3
      exact h3.symm.trans (Finset.sum_congr rfl fun k _ => σ.toLinearMap.map_smul _ _)
    rw [he]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Finset.sum_mul, map_sum, smul_mul_assoc, map_smul, key, smul_zero,
      Finset.sum_const_zero]
  have hw : J *ᵥ y = 0 := by
    funext i
    refine (traceForm_nondegenerate F E).1 _ fun e => ?_
    rw [Algebra.traceForm_apply, mul_comm]
    exact key2 i e
  have hy0 : y = 0 := Matrix.eq_zero_of_mulVec_eq_zero hJ.2 hw
  apply hv
  funext ⟨j, l⟩
  have := congrFun hy0 j
  have h2 := Fintype.linearIndependent_iff.1 b.linearIndependent (fun l => v (j, l)) this l
  simpa using h2

end CM

end GlobalTheory.CompanionTheory.SW.TraceFormGram

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW

theorem trace_form_coords : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∃ B : Matrix (Fin M × Fin d) (Fin M × Fin d) F, B.IsSymm ∧ B.det ≠ 0 ∧ ∀ (R : Type) [CommRing R] [Algebra F R] (x y : Fin M → R ⊗[F] E), Algebra.trace R (R ⊗[F] E) (hR R σ J x y) = (fun p : Fin M × Fin d => (Algebra.TensorProduct.basis R b).repr (x p.1) p.2) ⬝ᵥ (B.map (algebraMap F R) *ᵥ fun p : Fin M × Fin d => (Algebra.TensorProduct.basis R b).repr (y p.1) p.2) := by
  intro F E _ _ _ _ _ σ h M J hJ d b
  haveI : FiniteDimensional F E := Module.Basis.finiteDimensional_of_finite b
  refine ⟨TraceFormGram.trGram σ J b, TraceFormGram.trGram_isSymm h hJ b, TraceFormGram.trGram_det_ne_zero h hJ b, ?_⟩
  intro R _ _ x y
  have hh : hR R σ J x y = ∑ i, ∑ j, sigR R σ (x i) * ((1 : R) ⊗ₜ[F] J i j) * y j := rfl
  rw [hh]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, TraceFormGram.trace_entry σ b R]
  simp only [dotProduct, Matrix.mulVec, Fintype.sum_prod_type, Matrix.map_apply, TraceFormGram.trGram,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]

end GlobalTheory.CompanionTheory.SW
