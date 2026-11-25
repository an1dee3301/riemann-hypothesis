module

public import Mathlib
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.StageData
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Fin.Basic
public import Init.Data.Nat.Basic
public import Init.Data.NeZero
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.GroupWithZero.Units.Lemmas
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Indicator
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.ENNReal.Action
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.FieldTheory.Perfect
public import Mathlib.FieldTheory.Separable
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Module
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Finiteness.Defs
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
public import Mathlib.RingTheory.Trace.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Topology.Defs.Basic

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.StageValue

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]

theorem one_tmul_algebraMap (t : F) :
    (1 : R) ⊗ₜ[F] (algebraMap F E t) = (algebraMap F R t) ⊗ₜ[F] (1 : E) := by
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul,
    TensorProduct.smul_tmul']

theorem corner_half_trace_eq_of_pure_tensor [CharZero F] (hfr : Module.finrank F E = 2) {n : ℕ}
    (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) {x : R}
    (h : S 0 0 = x ⊗ₜ[F] (1 : E)) : s0 R S = x := by
  have hfin : Module.Finite F E := Module.finite_of_finrank_eq_succ hfr
  let b : Module.Basis (Fin 2) F E := Module.finBasisOfFinrankEq F E hfr
  have htr : Algebra.trace R (R ⊗[F] E) (x ⊗ₜ[F] (1 : E)) = 2 * x := by
    have h1 := Algebra.trace_algebraMap_of_basis (Algebra.TensorProduct.basis R b) x
    rw [Algebra.TensorProduct.algebraMap_apply] at h1
    simpa [two_mul, two_nsmul] using h1
  have h2 : algebraMap F R (1 / 2) * 2 = 1 := by
    calc algebraMap F R (1 / 2) * 2 = algebraMap F R (1 / 2) * algebraMap F R 2 := by rw [map_ofNat]
      _ = algebraMap F R (1 / 2 * 2) := (map_mul _ _ _).symm
      _ = 1 := by rw [show (1 / 2 * 2 : F) = 1 by norm_num, map_one]
  unfold s0
  rw [h, htr, ← mul_assoc, h2, one_mul]

theorem vec_one_zero {M n : ℕ} (X : Fin n → Fin M → R ⊗[F] E) :
    vec ((1 : R) ⊗ₜ[F] (1 : E)) (0 : Fin n → R ⊗[F] E) X = consTup X := by
  rw [← Algebra.TensorProduct.one_def]
  rfl

end Alg

section Main

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  (σ : E →ₐ[F] E) (t : F) (a : R → Rˣ) {n : ℕ}

theorem corner_half_trace_block_one [CharZero F] (hfr : Module.finrank F E = 2) (T : Matrix (Fin n) (Fin n) E) :
    s0 R ((blockOne (algebraMap F E t) T).map (inclR (F := F) R)) = algebraMap F R t := by
  apply corner_half_trace_eq_of_pure_tensor R hfr
  rw [← one_tmul_algebraMap]
  rfl

theorem cvec_block (T : Matrix (Fin n) (Fin n) E) :
    cvec R t a ((blockOne (algebraMap F E t) T).map (inclR R)) = 0 := by
  funext j
  simp [cvec, blockOne]

theorem schurM_block (T : Matrix (Fin n) (Fin n) E) :
    schurM R σ t a ((blockOne (algebraMap F E t) T).map (inclR R)) = T.map (inclR R) := by
  ext i j
  have hc := cvec_block R t a T
  simp only [schurM, hc, Pi.zero_apply, map_zero, zero_mul, sub_zero]
  simp [blockOne]

theorem schur_block (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b)
    (hT' : ∀ a b, σ (blockOne (algebraMap F E t) T b a) = blockOne (algebraMap F E t) T a b) :
    schur R σ t a (hermOf R σ _ hT') = hermOf R σ T hT := by
  apply Subtype.ext
  have hm : schurM R σ t a ((hermOf R σ _ hT' : HermR R σ (n + 1)) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) ∈ HermR R σ n := by
    show schurM R σ t a ((blockOne (algebraMap F E t) T).map (inclR R)) ∈ HermR R σ n
    rw [schurM_block]
    exact map_mem_HermR R σ T hT
  rw [schur_coe R σ t a _ hm]
  exact schurM_block R σ t a T

theorem isUnit_det_map (T : Matrix (Fin n) (Fin n) E) (hdet : T.det ≠ 0) :
    IsUnit (T.map (inclR (F := F) R)).det := by
  have h := (IsUnit.mk0 _ hdet).map (inclR (F := F) R)
  rw [RingHom.map_det] at h
  exact h

end Main

theorem family_at_block : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R) (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J)) (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0), StageData σ J t n b lam m₁ m' s B₀ a κ₁ cm → ∀ (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b), T.det ≠ 0 → ∀ (hT' : ∀ a b, σ (blockOne (algebraMap F E t) T b a) = blockOne (algebraMap F E t) T a b), hermOf R σ _ hT' ∈ (Bset R σ t a B₀ : Set (HermR R σ (n + 1))) ∧ fibS σ J t m₁ m' s B₀ a κ₁ cm (hermOf R σ _ hT') = cm 1 ^ n • ((m₁ (hermScal R σ (algebraMap F R t))).prod (m' (hermOf R σ T hT))).map (fun p => actW R σ _ (s p.1) (consTup p.2)) := by
  intro F E _ _ _ _ _ σ M J t n R _ _ _ _ _ d b lam m₁ m' s B₀ a κ₁ cm D T hT hdet hT'
  have hfr : Module.finrank F E = 2 := D.hCM.2.2.1
  have hs0 : s0 R ((hermOf R σ _ hT' : HermR R σ (n + 1)) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) = algebraMap F R t :=
    corner_half_trace_block_one R t hfr T
  have hsch := schur_block R σ t a T hT hT'
  have hmem : hermOf R σ _ hT' ∈ (Bset R σ t a B₀ : Set (HermR R σ (n + 1))) := by
    refine ⟨by rw [hs0]; exact D.htB, ?_⟩
    rw [hsch]
    exact isUnit_det_map R T hdet
  refine ⟨hmem, ?_⟩
  have hc : cvec R t a ((hermOf R σ _ hT' : HermR R σ (n + 1)) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) = 0 := cvec_block R t a T
  unfold fibS
  rw [Set.indicator_of_mem hmem]
  simp only [hs0, D.ha1, hsch, hc, D.hκ1, one_mul, Units.val_one, vec_one_zero]

end GlobalTheory.CompanionTheory.SW.StageValue
