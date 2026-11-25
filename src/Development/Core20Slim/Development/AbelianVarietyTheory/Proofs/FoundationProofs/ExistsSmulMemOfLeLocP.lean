module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.Foundations.ExistsUnitaryMulTriangular
public import Formalism.HermitianLattices.StatementLat
public import Formalism.LocalRingCardinality.DataCoeff
public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Init.Classical
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
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
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Attach
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Erase
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Sets
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Finite.Range
public import Mathlib.Data.Set.Operations
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Ideal.Prime

@[expose] public section

open GlobalTheory.DualWeyl MvPolynomial NumberField IsDedekindDomain
open Formalism.L2.DIV (colLat IsBasisAt dualFr)
open Formalism.HermitianLatticesTheory (localization₂)
open scoped Matrix

namespace GlobalTheory.DualWeylDual

variable {K : Type} [Field K] {N : ℕ}

theorem exists_smul_mem_of_le_locP (w : HeightOneSpectrum (𝓞 K)) {M M' : Submodule (𝓞 K) (Fin N → K)}
    (hM : M.FG) (h : M ≤ localization₂ w.asIdeal M') : ∃ t ∈ w.asIdeal.primeCompl, ∀ x ∈ M, t • x ∈ M' := by
  classical
  obtain ⟨s, rfl⟩ := hM
  have h1 : ∀ y : s, ∃ a ∈ w.asIdeal.primeCompl, a • (y : Fin N → K) ∈ M' := fun y =>
    h (Submodule.subset_span y.2)
  choose a ha0 ha using h1
  refine ⟨∏ y, a y, Submonoid.prod_mem _ fun y _ => ha0 y, fun x hx => ?_⟩
  induction hx using Submodule.span_induction with
  | mem y hy =>
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ (⟨y, hy⟩ : s)), mul_smul]
    exact M'.smul_mem _ (ha ⟨y, hy⟩)
  | zero => simp
  | add y z _ _ hy hz => rw [smul_add]; exact M'.add_mem hy hz
  | smul c y _ hy => rw [smul_comm]; exact M'.smul_mem _ hy

theorem localization_dualFr_le (w : HeightOneSpectrum (𝓞 K)) {M M' : Submodule (𝓞 K) (Fin N → K)}
    (hM : M.FG) (h : localization₂ w.asIdeal M ≤ localization₂ w.asIdeal M') :
    localization₂ w.asIdeal (dualFr M') ≤ localization₂ w.asIdeal (dualFr M) := by
  obtain ⟨t, ht, htM⟩ := exists_smul_mem_of_le_locP w hM
    (fun x hx => h ⟨1, Submonoid.one_mem _, by rwa [one_smul]⟩)
  rintro φ ⟨s, hs, hφ⟩
  refine ⟨t * s, Submonoid.mul_mem _ ht hs, fun x hx => ?_⟩
  have h1 : (s • φ) ⬝ᵥ (t • x) ∈ (1 : Submodule (𝓞 K) K) := hφ _ (htM x hx)
  rwa [dotProduct_smul, ← smul_dotProduct, smul_smul] at h1

theorem dualFr_colLat (B : GL (Fin N) K) : dualFr (colLat B) = colLat (Formalism.BasicNotions.inside₂ K N B) := by
  apply SetLike.ext
  intro φ
  rw [mem_colLat_iff]
  constructor
  · intro h
    have h1 : ∀ j, ∃ c : 𝓞 K, algebraMap (𝓞 K) K c = φ ⬝ᵥ fun a => (B : Matrix (Fin N) (Fin N) K) a j := fun j =>
      Submodule.mem_one.mp (h _ (Submodule.subset_span ⟨j, rfl⟩))
    choose c hc using h1
    refine ⟨c, ?_⟩
    have h2 : (fun j => (c j : K)) = (B : Matrix (Fin N) (Fin N) K)ᵀ *ᵥ φ := by
      funext j
      rw [Matrix.mulVec_transpose]
      exact hc j
    rw [h2, Matrix.mulVec_mulVec]
    change (((B⁻¹ : GL (Fin N) K) : Matrix (Fin N) (Fin N) K)ᵀ * _) *ᵥ φ = φ
    rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one, Matrix.one_mulVec]
  · rintro ⟨c, rfl⟩ x hx
    obtain ⟨d, rfl⟩ := (mem_colLat_iff _ _).mp hx
    change (((B⁻¹ : GL (Fin N) K) : Matrix (Fin N) (Fin N) K)ᵀ *ᵥ _) ⬝ᵥ _ ∈ _
    rw [Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
    refine Submodule.mem_one.mpr ⟨c ⬝ᵥ d, ?_⟩
    simp [dotProduct]

theorem isBasisAt_dualFr (w : HeightOneSpectrum (𝓞 K)) {L : Submodule (𝓞 K) (Fin N → K)} (hL : L.FG)
    {B : GL (Fin N) K} (hB : IsBasisAt w L B) : IsBasisAt w (dualFr L) (Formalism.BasicNotions.inside₂ K N B) := by
  unfold IsBasisAt at hB ⊢
  rw [← dualFr_colLat]
  exact le_antisymm (localization_dualFr_le w (Submodule.fg_span (Set.finite_range _)) hB.ge) (localization_dualFr_le w hL hB.le)

end GlobalTheory.DualWeylDual
