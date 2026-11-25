module

public import Mathlib
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Nat.Basic
public import Init.Data.Nat.Div.Basic
public import Init.Data.Zero
public import Init.Ext
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Order.Kleene
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Order.ZeroLEOne
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Order.Lattice
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.Real.Star
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Set.CoeSort
public import Mathlib.Data.Set.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Order.Filter.AtTopBot.Tendsto
public import Mathlib.Order.Filter.Basic
public import Mathlib.Order.Filter.Cofinite
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Filter.Tendsto
public import Mathlib.Order.Lattice
public import Mathlib.Order.Max
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.RestrictedProduct.Basic
public import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.DenseEmbedding
public import Mathlib.Topology.Maps.Basic
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
public import Mathlib.Topology.Metrizable.Basic
public import Mathlib.Topology.Metrizable.Uniformity
public import Mathlib.Topology.Order.Basic
public import Mathlib.Topology.Order.OrderClosed
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open Filter Topology NumberField IsDedekindDomain

private lemma UpperTheory.Reformulated.B.AdelicCharacterNormOne.factorial_tendsto_zero {K : Type*} [NormedField K]
    (h1 : ∀ n : ℕ, ‖(n : K)‖ ≤ 1) (N : ℕ) (hN : 0 < N) (hlt : ‖(N : K)‖ < 1) :
    Tendsto (fun n : ℕ => ((n.factorial : ℕ) : K)) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine tendsto_order.2 ⟨fun a ha => Eventually.of_forall fun n => ha.trans_le (norm_nonneg _),
    fun a ha => ?_⟩
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one ha hlt
  filter_upwards [eventually_ge_atTop (N ^ k)] with n hn
  obtain ⟨m, hm⟩ := Nat.dvd_factorial (pow_pos hN k) hn
  rw [hm, Nat.cast_mul, Nat.cast_pow, norm_mul, norm_pow]
  exact (mul_le_of_le_one_right (by positivity) (h1 m)).trans_lt hk

private lemma UpperTheory.Reformulated.B.AdelicCharacterNormOne.local_tendsto {F : Type} [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) :
    Tendsto (fun n : ℕ => ((n.factorial : ℕ) : v.adicCompletion F)) atTop (𝓝 0) := by
  refine UpperTheory.Reformulated.B.AdelicCharacterNormOne.factorial_tendsto_zero (K := v.adicCompletion F) (fun n => ?_)
    (Ideal.absNorm v.asIdeal) (zero_lt_one.trans (HeightOneSpectrum.one_lt_absNorm v)) ?_
  · have := FinitePlace.norm_le_one F v (n : 𝓞 F)
    rwa [map_natCast, map_natCast] at this
  · have := (FinitePlace.norm_lt_one_iff_mem F v _).2 (Ideal.absNorm_mem v.asIdeal)
    rwa [map_natCast, map_natCast] at this

private lemma UpperTheory.Reformulated.B.AdelicCharacterNormOne.finite_tendsto {F : Type} [Field F] [NumberField F] :
    Tendsto (fun n : ℕ => ((n.factorial : ℕ) : FiniteAdeleRing (𝓞 F) F)) atTop (𝓝 0) := by
  have h : Tendsto (fun (n : ℕ) (v : HeightOneSpectrum (𝓞 F)) =>
      ((n.factorial : ℕ) : v.adicCompletionIntegers F)) atTop (𝓝 0) := by
    rw [tendsto_pi_nhds]
    intro v
    rw [tendsto_subtype_rng]
    simpa using UpperTheory.Reformulated.B.AdelicCharacterNormOne.local_tendsto v
  have hc := (RestrictedProduct.isEmbedding_structureMap
    (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
    (𝓕 := cofinite)).continuous
  exact (hc.tendsto _).comp h

private lemma UpperTheory.Reformulated.B.AdelicCharacterNormOne.eq_one_of_tendsto {r : ℝ} (hr : 0 ≤ r)
    (h : Tendsto (fun n : ℕ => r ^ n.factorial) atTop (𝓝 1)) : r = 1 := by
  have hf : Tendsto Nat.factorial atTop atTop :=
    tendsto_atTop_mono Nat.self_le_factorial tendsto_id
  rcases lt_trichotomy r 1 with hlt | heq | hgt
  · exact absurd (tendsto_nhds_unique ((tendsto_pow_atTop_nhds_zero_of_lt_one hr hlt).comp hf) h)
      zero_ne_one
  · exact heq
  · exact absurd h (not_tendsto_nhds_of_tendsto_atTop
      ((tendsto_pow_atTop_atTop_of_one_lt hgt).comp hf) 1)

theorem UpperTheory.Reformulated.B.AdelicCharacterNormOne.norm_eq_one :
    ∀ {F : Type} [inst : Field F] [inst_1 : NumberField F]
    (ψ : AddChar (NumberField.AdeleRing (NumberField.RingOfIntegers F) F) ℂ),
    Continuous (⇑ψ : NumberField.AdeleRing (NumberField.RingOfIntegers F) F → ℂ) →
      (∀ (a : F),
          (ψ : NumberField.AdeleRing (NumberField.RingOfIntegers F) F → ℂ)
              ((Algebra.algebraMap F (NumberField.AdeleRing (NumberField.RingOfIntegers F) F) :
                  F → NumberField.AdeleRing (NumberField.RingOfIntegers F) F)
                a) =
            (1 : ℂ)) →
        ∀ (x : NumberField.AdeleRing (NumberField.RingOfIntegers F) F),
          ‖(ψ : NumberField.AdeleRing (NumberField.RingOfIntegers F) F → ℂ) x‖ = (1 : ℝ) := by
  intro F _ _ ψ hψ htriv
  let i : InfiniteAdeleRing F → AdeleRing (𝓞 F) F := fun x => (x, 0)
  let j : FiniteAdeleRing (𝓞 F) F → AdeleRing (𝓞 F) F := fun y => (0, y)
  have hi : Continuous i := continuous_id.prodMk continuous_const
  have hj : Continuous j := continuous_const.prodMk continuous_id
  have hsplit : ∀ x : AdeleRing (𝓞 F) F, x = i x.1 + j x.2 := fun x =>
    Prod.ext (add_zero x.1).symm (zero_add x.2).symm
  have hfin : ∀ y, ‖ψ (j y)‖ = 1 := by
    intro y
    apply UpperTheory.Reformulated.B.AdelicCharacterNormOne.eq_one_of_tendsto (norm_nonneg _)
    have h1 := (UpperTheory.Reformulated.B.AdelicCharacterNormOne.finite_tendsto (F := F)).mul_const y
    rw [zero_mul] at h1
    have h2 := (((hψ.comp hj).norm).tendsto 0).comp h1
    have h0 : j 0 = 0 := rfl
    have hs : ∀ n : ℕ, j ((n : FiniteAdeleRing (𝓞 F) F) * y) = n • j y := fun n =>
      Prod.ext (nsmul_zero n).symm (nsmul_eq_mul n y).symm
    simp only [Function.comp_def, h0, hs, AddChar.map_zero_eq_one, norm_one,
      AddChar.map_nsmul_eq_pow, norm_pow] at h2
    exact h2
  have hinf : ∀ x, ‖ψ (i x)‖ = 1 := by
    intro x
    refine (InfiniteAdeleRing.denseRange_algebraMap F).induction_on x
      (isClosed_eq (hψ.comp hi).norm continuous_const) fun a => ?_
    have h := congrArg norm (htriv a)
    rw [hsplit (algebraMap F _ a), AddChar.map_add_eq_mul, norm_mul, hfin, mul_one, norm_one] at h
    exact h
  intro x
  rw [hsplit x, AddChar.map_add_eq_mul, norm_mul, hfin, hinf, mul_one]
