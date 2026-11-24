module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSelfDualE
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.PairingNondegenerateHolds
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkPderivBlockEmbNe
public import Formalism.GradedWeylDivisibility.StatementE
public import Formalism.HarderNarasimhan.ShiftInvariance
public import Formalism.QuotientMetricDivisors.ReductionLemmaZero
public import Formalism.QuotientMetricDivisors.ProdFormula
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.MeanMaxLeaf.LeafMMFree
public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.DivIntoDual
public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ValBasic
public import Formalism.GradedWeylDivisibility.StatementD
public import Formalism.HermitianLattices.StatementLat
public import Formalism.LocalRingCardinality.DataCoeff
public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Formalism.QuotientMetricDivisors.Statement
public import Init.Classical
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Nat.Lemmas
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Divisibility.Basic
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Associated
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Module.Submodule.Map
public import Mathlib.Algebra.Module.Submodule.Pointwise
public import Mathlib.Algebra.Module.Submodule.Range
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.Algebra.Order.Kleene
public import Mathlib.Algebra.Order.Monoid.Associated
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.DedekindDomain.Factorization
public import Mathlib.RingTheory.DedekindDomain.Ideal.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.FractionalIdeal.Basic
public import Mathlib.RingTheory.FractionalIdeal.Operations
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Ideal.Prime
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.RingTheory.UniqueFactorizationDomain.FactorSet

@[expose] public section

open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder

namespace GlobalTheory.LocInt

variable {K : Type} [Field K] [NumberField K]

theorem vw_eq_zero_of_notMem (w : HeightOneSpectrum (𝓞 K)) {s : 𝓞 K} (hs : s ∉ w.asIdeal) :
    vw w (s : K) = 0 := by
  classical
  have hs0 : s ≠ 0 := by
    rintro rfl
    exact hs w.asIdeal.zero_mem
  have hJ : (Ideal.span {s} : Ideal (𝓞 K)) ≠ 0 := by
    rwa [ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
  unfold vw
  rw [← FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.count_coe K w hJ]
  have hm : Associates.mk (Ideal.span {s} : Ideal (𝓞 K)) ≠ 0 := by rwa [ne_eq, Associates.mk_eq_zero]
  by_contra h
  have h1 : 1 ≤ (Associates.mk w.asIdeal).count (Associates.mk (Ideal.span {s} : Ideal (𝓞 K))).factors := by
    apply Nat.one_le_iff_ne_zero.2
    intro h0
    exact h (by rw [h0]; rfl)
  rw [← Associates.prime_pow_dvd_iff_le hm w.associates_irreducible, pow_one,
    Associates.mk_le_mk_iff_dvd, Ideal.dvd_span_singleton] at h1
  exact hs h1

theorem exists_map_eq_of_mem_nabStd {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) {F : Pol K ι n}
    (hF : F ∈ nabStd K lam) : F ∈ LinearMap.range (toK K (ι × Fin n × Fin n)) := by
  refine (Submodule.span_le.2 ?_ : nabStd K lam ≤ _) hF
  rintro P ⟨G, hG, rfl⟩
  choose Q _ hQ using fun τ => Submodule.mem_map.1 (hG τ)
  refine ⟨∏ τ, Formalism.GradedWeylDivisibility.blockEmb (𝓞 K) τ (Q τ), ?_⟩
  change MvPolynomial.map (algebraMap (𝓞 K) K) _ = _
  rw [map_prod]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [← hQ τ]
  simp only [Formalism.GradedWeylDivisibility.blockEmb]
  exact map_rename _ _ _

theorem localIntegrality : ∀ (K : Type) [Field K] [NumberField K] [StarRing K], (∀ a : K, (∀ w : HeightOneSpectrum (𝓞 K), 0 ≤ vw w a) → a ∈ (algebraMap (𝓞 K) K).range) ∧ ∀ (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n) (w : HeightOneSpectrum (𝓞 K)) (F : Pol K ι n), F ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (nabStd K lam) → ∀ mo, 0 ≤ vw w (AddMonoidAlgebra.coeff F mo) := by
  intro K _ _ _
  refine ⟨fun a h => ?_, fun ι _ n lam w F hF mo => ?_⟩
  · by_cases ha : a = 0
    · subst ha
      exact zero_mem _
    · exact DualLatticeDivisor.mem_range_of_vw_nonneg a ha h
  · obtain ⟨s, hs, hsF⟩ := hF
    obtain ⟨Q, hQ⟩ := exists_map_eq_of_mem_nabStd lam hsF
    by_cases hc : AddMonoidAlgebra.coeff F mo = 0
    · rw [hc, ValuationRepresentative.vw_zero]
    have hs' : s ∉ w.asIdeal := hs
    have hs0 : (s : K) ≠ 0 := by
      intro h0
      have : s = 0 := RingOfIntegers.ext h0
      exact hs' (this ▸ w.asIdeal.zero_mem)
    have hco : (s : K) * AddMonoidAlgebra.coeff F mo = ((AddMonoidAlgebra.coeff Q mo : 𝓞 K) : K) := by
      have h1 := congrArg (AddMonoidAlgebra.coeff · mo) hQ
      rw [coeff_smul] at h1
      have h2 : AddMonoidAlgebra.coeff (toK K _ Q) mo = ((AddMonoidAlgebra.coeff Q mo : 𝓞 K) : K) := coeff_map _ _ _
      rw [← h2, h1, Algebra.smul_def]
    have h3 := ValuationRepresentative.vw_int_nonneg w (AddMonoidAlgebra.coeff Q mo)
    rwa [← hco, ValuationRepresentative.vw_mul w _ _ hs0 hc, vw_eq_zero_of_notMem w hs', zero_add] at h3

end GlobalTheory.LocInt
