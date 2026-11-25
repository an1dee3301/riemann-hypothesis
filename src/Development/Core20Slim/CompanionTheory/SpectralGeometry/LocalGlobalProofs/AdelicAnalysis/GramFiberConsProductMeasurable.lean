module

public import Mathlib
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.StageData
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorInvolutionAlgebraProperties
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramBlockOneFirstVectorFormulaStatement
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.BlockOneScalarPreservesNondegenerateStatement
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Fin.Basic
public import Init.Data.Fin.Lemmas
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
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.Nontrivial.Defs
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.FieldTheory.Perfect
public import Mathlib.FieldTheory.Separable
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.Artinian.Defs
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Free
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.Trace.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Separation.Hausdorff

@[expose] public section

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.PiLocalization₂.GramCoord

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

section Alg

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]

theorem corner_half_trace_of_pure_tensor (hfr : Module.finrank F E = 2) {n : ℕ}
    (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) (r : R)
    (h : S 0 0 = r ⊗ₜ[F] (1 : E)) : s0 R S = r := by
  rcases subsingleton_or_nontrivial R with h' | h'
  · exact Subsingleton.elim _ _
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by omega)
  have hK : Module.finrank R (R ⊗[F] E) = 2 := by rw [Module.finrank_baseChange]; exact hfr
  have hc : (r ⊗ₜ[F] (1 : E) : R ⊗[F] E) = algebraMap R (R ⊗[F] E) r := rfl
  have h2 : algebraMap F R (1 / 2) * 2 = 1 := by
    have : (2 : R) = algebraMap F R 2 := (map_ofNat (algebraMap F R) 2).symm
    rw [this, ← map_mul]; simp
  unfold s0
  rw [h, hc, Algebra.trace_algebraMap, hK, two_nsmul, ← two_mul, ← mul_assoc, h2, one_mul]

variable [NumberField E]

theorem gram_symm (σ : E →ₐ[F] E) (hinv : ∀ y, sigR R σ (sigR R σ y) = y) {M n : ℕ}
    {J : Matrix (Fin M) (Fin M) E} (hJ : ∀ i j, σ (J j i) = J i j)
    (X : Fin n → Fin M → R ⊗[F] E) (p q : Fin n) :
    sigR R σ (gramR R σ J X q p) = gramR R σ J X p q := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [gramR, hR, hform, JR, map_sum, map_mul, hinv, Matrix.map_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have h : sigR R σ (inclR R (J j i)) = inclR R (J i j) := by
    rw [← hJ i j]; simp [sigR, inclR]
  rw [h]; ring

theorem schurM_mem (σ : E →ₐ[F] E) (hinv : ∀ y, sigR R σ (sigR R σ y) = y) {n : ℕ} (t : F) (a : R → Rˣ)
    (S : HermR R σ (n + 1)) :
    schurM R σ t a (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) ∈ HermR R σ n := by
  intro i j
  have hS : sigR R σ ((S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) j.succ i.succ) =
      (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) i.succ j.succ := S.2 i.succ j.succ
  have hi : sigR R σ (inclR R (algebraMap F E t)) = inclR R (algebraMap F E t) := by
    simp [sigR, inclR]
  simp only [schurM, map_sub, map_mul, hinv, hS, hi]
  ring

end Alg

theorem unit_tmul {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R] [Algebra F R]
    {t : F} (ht : t ≠ 0) (u : Rˣ) :
    ((((u⁻¹ : Rˣ) : R) ⊗ₜ[F] (algebraMap F E t⁻¹)) * (((u : Rˣ) : R) ⊗ₜ[F] (algebraMap F E t)) : R ⊗[F] E) = 1 := by
  rw [Algebra.TensorProduct.tmul_mul_tmul, Units.inv_mul, ← map_mul, inv_mul_cancel₀ ht, map_one]
  rfl

theorem coords : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R) (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J)) (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0), StageData σ J t n b lam m₁ m' s B₀ a κ₁ cm → (∀ x ∈ B₀, ∀ (c : Fin n → R ⊗[F] E) (X : Fin n → Fin M → R ⊗[F] E) (S : HermR R σ (n + 1)), (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) = gramR R σ (blockOne (algebraMap F E t) J) (vec (((a x : Rˣ) : R) ⊗ₜ[F] (1 : E)) c X) → s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) = x ∧ cvec R t a (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) = c ∧ (schur R σ t a S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) = gramR R σ J X) ∧ (∀ (S : HermR R σ (n + 1)) (X : Fin n → Fin M → R ⊗[F] E), s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) ∈ B₀ → gramR R σ J X = (schur R σ t a S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) → gramR R σ (blockOne (algebraMap F E t) J) (vec (((a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)))) : R) ⊗ₜ[F] (1 : E)) (cvec R t a (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))) X) = (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))) := by
  intro F E _ _ _ _ _ σ M J t n R _ _ _ _ _ d b lam m₁ m' s B₀ a κ₁ cm D
  obtain ⟨-, -, -, -, hart, hred, -⟩ := D.hR
  haveI := hart
  haveI := hred
  obtain ⟨-, -, -, hinv, -, hfix, -⟩ := GlobalTheory.CompanionTheory.SW.KAlg.algebra_tensor_invol F E σ D.hCM R
  have hfr : Module.finrank F E = 2 := D.hCM.2.2.1
  have ht : t ≠ 0 := D.ht
  have hJ' := GlobalTheory.T.block_one_scalar_preserves_nondegenerate F E σ M J D.hJ t ht
  refine ⟨?_, ?_⟩
  · intro x hx c X S hS
    obtain ⟨h00, h0j, hij⟩ := GlobalTheory.T.gram_block_one_first_vector_formula F E σ M J t n R ((a x : Rˣ) : R) c X
    rw [← hS] at h00 h0j hij
    have hx0 : (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) 0 0 = x ⊗ₜ[F] (1 : E) := by
      rw [h00, ← D.hsq x hx]
    have hs0 := corner_half_trace_of_pure_tensor R hfr _ x hx0
    have hc : cvec R t a (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) = c := by
      funext j
      simp only [cvec]
      rw [hs0, h0j j, ← mul_assoc, unit_tmul ht, one_mul]
    refine ⟨hs0, hc, ?_⟩
    rw [schur_coe R σ t a S (schurM_mem R σ hinv t a S)]
    ext i j
    simp only [schurM]
    rw [hc, hij i j, add_sub_cancel_left]
  · intro S X hB hX
    obtain ⟨h00, h0j, hij⟩ := GlobalTheory.T.gram_block_one_first_vector_formula F E σ M J t n R
      ((a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))) : Rˣ) : R)
      (cvec R t a (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))) X
    have hH := gram_symm R σ hinv hJ'.1 (vec
      (((a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))) : Rˣ) : R) ⊗ₜ[F] (1 : E))
      (cvec R t a (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))) X)
    obtain ⟨r, hr⟩ := hfix ((S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) 0 0) (S.2 0 0)
    have hsr := corner_half_trace_of_pure_tensor R hfr _ r hr
    have hrow : ∀ j : Fin n, gramR R σ (blockOne (algebraMap F E t) J) (vec
        (((a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))) : Rˣ) : R) ⊗ₜ[F] (1 : E))
        (cvec R t a (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))) X) 0 j.succ =
        (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) 0 j.succ := by
      intro j
      rw [h0j j]
      simp only [cvec]
      rw [← mul_assoc, mul_comm (_ ⊗ₜ[F] (algebraMap F E t)), unit_tmul ht, one_mul]
    ext i j
    refine Fin.cases ?_ (fun i => ?_) i
    · refine Fin.cases ?_ (fun j => ?_) j
      · rw [h00, hr, ← D.hsq _ hB, hsr]
      · exact hrow j
    · refine Fin.cases ?_ (fun j => ?_) j
      · rw [← hH i.succ 0, hrow i]
        exact S.2 i.succ 0
      · rw [hij i j, congrFun (congrFun hX i) j, schur_coe R σ t a S (schurM_mem R σ hinv t a S)]
        simp only [schurM]
        rw [add_sub_cancel]

end GlobalTheory.CompanionTheory.SW.PiLocalization₂.GramCoord
