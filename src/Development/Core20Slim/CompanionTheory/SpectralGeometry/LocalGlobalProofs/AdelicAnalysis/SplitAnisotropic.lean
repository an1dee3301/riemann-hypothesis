module

public import Mathlib
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import Batteries.Logic
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Fin.Basic
public import Init.Data.Fin.Lemmas
public import Init.Data.Function
public import Init.Data.Int.Basic
public import Init.Data.Int.Lemmas
public import Init.Data.Int.Order
public import Init.Data.Nat.Basic
public import Init.Data.NeZero
public import Init.Data.Zero
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Submonoid.BigOperators
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Pi
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.GroupWithZero.Units.Lemmas
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Ker
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Module.Submodule.Range
public import Mathlib.Algebra.Module.Torsion.Pi
public import Mathlib.Algebra.NeZero
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
public import Mathlib.Data.Fin.SuccPred
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.Dimension.Localization
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.Bialgebra.Basic
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TotallySplit
public import Mathlib.Tactic.FieldSimp.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.AlgSplit

theorem det_blockOne {K : Type} [CommRing K] {M : ℕ} (t : K) (A : Matrix (Fin M) (Fin M) K) :
    (blockOne t A).det = t * A.det := by
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  have hz : ∀ j : Fin M, blockOne t A 0 j.succ = 0 := by intro j; simp [blockOne]
  have h00 : blockOne t A 0 0 = t := by simp [blockOne]
  have h0 : (blockOne t A).submatrix Fin.succ Fin.succ = A := by
    ext i j; simp [blockOne]
  simp [hz, h00, h0]

theorem split_anisotropic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E), IsHermND σ J → ∀ (t : F) (x : Fin (M + 1) → E), t ≠ 0 → hE σ J x x = algebraMap F E t → ∃ (g : GL (Fin (M + 1)) E) (J₁ : Matrix (Fin M) (Fin M) E), IsHermND σ J₁ ∧ blockOne (algebraMap F E t) J₁ = cT (σ : E →+* E) (g : Matrix (Fin (M + 1)) (Fin (M + 1)) E) * J * g ∧ ∀ i, (g : Matrix (Fin (M + 1)) (Fin (M + 1)) E) i 0 = x i := by
  intro F E _ _ _ _ _ σ hCM M J hJ t x ht hx
  obtain ⟨-, -, -, hconj⟩ := hCM
  have hσ : ∀ e : E, σ (σ e) = e := by
    intro e
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    rw [hconj, hconj, star_star]
  have hherm : ∀ y z, σ (hE σ J y z) = hE σ J z y := by
    intro y z
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hE, hform, map_sum, map_mul, AlgHom.coe_toRingHom, RingHom.coe_coe, hσ]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hJ.1 i j]
    ring
  set s : E := algebraMap F E t with hs
  have hs0 : s ≠ 0 := (map_ne_zero _).2 ht
  let φ : (Fin (M + 1) → E) →ₗ[E] E :=
    { toFun := fun y => hE σ J x y
      map_add' := by
        intro y z
        simp [hE, hform, mul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro c y
        simp only [hE, hform, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        ring }
  have hφ : ∀ y, φ y = hE σ J x y := fun _ => rfl
  have hsurj : Function.Surjective φ := fun e =>
    ⟨(e / s) • x, by rw [map_smul, hφ, hx, smul_eq_mul]; field_simp⟩
  have hfr : Module.finrank E (LinearMap.ker φ) = M := by
    have h := LinearMap.finrank_range_add_finrank_ker φ
    rw [LinearMap.range_eq_top.2 hsurj, finrank_top] at h
    simp at h
    omega
  let b := Module.finBasisOfFinrankEq E (LinearMap.ker φ) hfr
  have hb : ∀ k, hE σ J x (b k : Fin (M + 1) → E) = 0 := fun k => (b k).2
  let col : Fin (M + 1) → Fin (M + 1) → E := Fin.cons x (fun k => (b k : Fin (M + 1) → E))
  let gm : Matrix (Fin (M + 1)) (Fin (M + 1)) E := Matrix.of fun i j => col j i
  have hG : ∀ i j, (cT (σ : E →+* E) gm * J * gm) i j = hE σ J (col i) (col j) := by
    intro i j
    simp only [cT, Matrix.mul_apply, hE, hform, gm, Matrix.transpose_apply, Matrix.map_apply,
      Matrix.of_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
  have hdet : gm.det ≠ 0 := by
    intro h0
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    have hsum : v 0 • x + ∑ k : Fin M, v k.succ • (b k : Fin (M + 1) → E) = 0 := by
      rw [← hv]
      ext i
      simp [gm, col, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mul_comm]
    have hv00 : v 0 = 0 := by
      have h1 := congrArg φ hsum
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_add (f := _), map_smul, map_sum, map_zero, hφ, hx, smul_eq_mul] at h1
      have h2 : ∀ k : Fin M, φ (v k.succ • (b k : Fin (M + 1) → E)) = 0 := by
        intro k
        rw [map_smul, hφ, hb, smul_zero]
      simp only [h2, Finset.sum_const_zero, add_zero] at h1
      exact (mul_eq_zero.1 h1).resolve_right hs0
    have hker : ∑ k : Fin M, v k.succ • b k = 0 := by
      apply Subtype.ext
      rw [hv00, zero_smul, zero_add] at hsum
      simpa using hsum
    have hvs := Fintype.linearIndependent_iff.1 b.linearIndependent _ hker
    apply hv0
    ext i
    refine Fin.cases hv00 hvs i
  let J₁ : Matrix (Fin M) (Fin M) E := Matrix.of fun k l =>
    hE σ J (b k : Fin (M + 1) → E) (b l : Fin (M + 1) → E)
  have hblock : blockOne s J₁ = cT (σ : E →+* E) gm * J * gm := by
    ext i j
    rw [hG]
    refine Fin.cases ?_ (fun k => ?_) i <;> refine Fin.cases ?_ (fun l => ?_) j
    · simp [blockOne, col, hx, hs]
    · simp [blockOne, col, hb]
    · have h3 : hE σ J (b k : Fin (M + 1) → E) x = 0 := by
        rw [← hherm, hb, map_zero]
      simp [blockOne, col, h3]
    · simp [blockOne, col, J₁]
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero gm hdet, J₁, ⟨?_, ?_⟩, hblock, fun i => rfl⟩
  · intro k l
    exact hherm _ _
  · intro hJ0
    have h4 := congrArg Matrix.det hblock
    rw [det_blockOne, hJ0, mul_zero, Matrix.det_mul, Matrix.det_mul] at h4
    have h5 : (cT (σ : E →+* E) gm).det = σ gm.det := by
      rw [cT, Matrix.det_transpose]
      exact ((σ : E →+* E).map_det gm).symm
    rw [h5] at h4
    have h6 : σ gm.det ≠ 0 := (map_ne_zero _).2 hdet
    exact mul_ne_zero (mul_ne_zero h6 hJ.2) hdet h4.symm

end GlobalTheory.CompanionTheory.SW.AlgSplit
