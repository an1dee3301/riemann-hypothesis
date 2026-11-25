module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.IsHermForm
public import Formalism.LocalToGlobal.ProjectiveLattices.ThClass
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicCompletionRationalPointsAndApproximation
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsUnitaryOfSelfDual
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Init.ByCases
public import Init.Classical
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Nat.Basic
public import Init.Data.Nat.Coprime
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.GroupWithZero.Action
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Divisibility.Basic
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Pi
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.GroupWithZero.Units.Lemmas
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Basic
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Ker
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Algebra.Order.ZeroLEOne
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Complex.BigOperators
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.NNRat.Defs
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Rat.Defs
public import Mathlib.Data.Rat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.FieldTheory.Separable
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.CMField
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.Order.BoundedOrder.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal

@[expose] public section

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open scoped TensorProduct Matrix

namespace GlobalTheory.AdelTranslate

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}























end General

section Lattice

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem span_eq_top (Λ : GenLat E n) (hU : Λ.Unimod) : Submodule.span E (Λ.La : Set (Fin n → E)) = ⊤ := by
  classical
  by_contra hne
  obtain ⟨φ, hφ0, hφ⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
  let v : Fin n → E := fun j => IsCMField.complexConj E (φ (Pi.single j 1))
  have hv : ∀ w : Fin n → E, ∑ j, IsCMField.complexConj E (v j) * w j = φ w := fun w => by
    rw [LinearMap.pi_apply_eq_sum_univ φ w]
    refine Finset.sum_congr rfl fun j _ => ?_
    have : (fun i => if j = i then (1 : E) else 0) = Pi.single j 1 := by
      funext i
      simp [Pi.single_apply, eq_comm]
    simp [v, this, mul_comm]
  have h0 : ∀ w ∈ Λ.La, φ w = 0 := fun w hw => hφ (Submodule.subset_span hw)
  have hvΛ : v ∈ Λ.La := (hU v).2 fun w hw => by
    rw [hv, h0 w hw]
    exact zero_mem _
  have h1 : ∑ j, IsCMField.complexConj E (v j) * v j = 0 := (hv v).trans (h0 v hvΛ)
  obtain ⟨σ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have h2 : ∑ j, Complex.normSq (σ (v j)) = 0 := by
    have := congrArg σ h1
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, IsCMField.complexEmbedding_complexConj, map_zero,
      ← Complex.normSq_eq_conj_mul_self] at this
    exact_mod_cast this
  have h3 : ∀ j, v j = 0 := fun j => by
    have := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => Complex.normSq_nonneg _).1 h2 j (Finset.mem_univ j)
    simpa using this
  refine hφ0 (LinearMap.ext fun w => ?_)
  rw [← hv]
  simp [h3]

omit [IsCMField E] in
theorem span_smul_le_iff (k : ℕ) (L₁ L₂ : Submodule (𝓞 E) (Fin n → E)) :
    Ideal.span {(k : 𝓞 E)} • L₁ ≤ L₂ ↔ ∀ x ∈ L₁, k • x ∈ L₂ := by
  constructor
  · intro h x hx
    have := h (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) hx)
    rwa [Nat.cast_smul_eq_nsmul] at this
  · intro h
    refine Submodule.smul_le.2 fun r hr x hx => ?_
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hr
    rw [mul_smul, Nat.cast_smul_eq_nsmul]
    exact L₂.smul_mem a (h x hx)

theorem exists_pos (Λ : GenLat E n) (hU : Λ.Unimod) {M : ℕ} (hT : Λ.TrivAt M) :
    ∃ k : ℕ, 0 < k ∧ k.Coprime M ∧ (∀ x ∈ Λ.La, k • x ∈ stdLat E n) ∧ ∀ x ∈ stdLat E n, k • x ∈ Λ.La := by
  classical
  obtain ⟨k, hk, h₁, h₂⟩ := hT
  rcases Nat.eq_zero_or_pos k with rfl | hpos
  · obtain rfl : M = 1 := by simpa using hk
    choose d hd hdx using fun j : Fin n => cap_exists_denom Λ.La (span_eq_top Λ hU) (Pi.single j 1)
    have hs : ∀ j, (∏ i, d i) • (Pi.single j 1 : Fin n → E) ∈ Λ.La := fun j => by
      obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem d (Finset.mem_univ j)
      rw [hc, mul_comm, mul_smul]
      exact nsmul_mem (hdx j) c
    refine ⟨∏ i, d i, Finset.prod_pos fun i _ => hd i, by simp, fun x hx j _ => ?_, fun x hx => ?_⟩
    · obtain ⟨a, ha⟩ := (hU _).1 (hs j) x hx
      refine Submodule.mem_one.2 ⟨a, ha.trans ?_⟩
      simp [Pi.single_apply, apply_ite]
    · rw [← Finset.univ_sum_single x, Finset.smul_sum]
      refine Submodule.sum_mem _ fun j _ => ?_
      obtain ⟨a, ha⟩ := Submodule.mem_one.1 (hx j (Set.mem_univ j))
      convert Λ.La.smul_mem a (hs j) using 1
      rw [smul_comm a]
      congr 1
      funext i
      simp [Pi.single_apply, Algebra.smul_def, ← ha]
  · exact ⟨k, hpos, hk, (span_smul_le_iff _ _ _).1 h₁, (span_smul_le_iff _ _ _).1 h₂⟩

end Lattice


end GlobalTheory.AdelTranslate
