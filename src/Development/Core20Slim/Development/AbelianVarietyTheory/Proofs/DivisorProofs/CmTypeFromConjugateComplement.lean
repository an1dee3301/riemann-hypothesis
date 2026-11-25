module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TamagawaSpecialUnitary
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasSign
public import Formalism.FrobeniusOrbits.Statement
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ZsmulGeneratorEqZeroOfProjection
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Function
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Ring.Commute
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.NNRat.Defs
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Cast.Order.Ring
public import Mathlib.Data.Rat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Logic.Function.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2    
open scoped TensorProduct

namespace GlobalTheory.MassLink

theorem tauE_injective' (D : D7) : Function.Injective (TH.tauE D) := fun _ _ h =>
  D.eTau.injective (Subtype.ext ((Formalism.BasicNotions.factEmb D.R D.host).1.1 h))

theorem tauE_surj' (D : D7) (φ : D.host.E →+* ℂ)
    (h : φ D.host.sqrtMinusD = Complex.I * (Real.sqrt D.host.d : ℂ)) : ∃ ρ, TH.tauE D ρ = φ := by
  obtain ⟨g, rfl⟩ := (Formalism.BasicNotions.factEmb D.R D.host).1.2 φ
  exact ⟨D.eTau.symm ⟨g, ((Formalism.BasicNotions.factEmb D.R D.host).2 g).1 h⟩, by unfold TH.tauE; rw [Equiv.apply_symm_apply]⟩

theorem tauE_or' (D : D7) (φ : D.host.E →+* ℂ) :
    ∃ ρ, TH.tauE D ρ = φ ∨ TH.tauE D ρ = ComplexEmbedding.conjugate φ := by
  have h0 : D.host.φ₀ D.host.sqrtMinusD = Complex.I * (Real.sqrt D.host.d : ℂ) := D.host.φ₀_mem
  have hs : D.host.sqrtMinusD * D.host.sqrtMinusD = -(D.host.d : D.host.E) := by
    apply D.host.φ₀.injective
    rw [map_mul, h0, map_neg, map_natCast, mul_mul_mul_comm, Complex.I_mul_I, ← Complex.ofReal_mul,
      Real.mul_self_sqrt (Nat.cast_nonneg _)]
    simp
  have h1 : φ D.host.sqrtMinusD * φ D.host.sqrtMinusD =
      (Complex.I * (Real.sqrt D.host.d : ℂ)) * (Complex.I * (Real.sqrt D.host.d : ℂ)) := by
    rw [← map_mul, hs, ← h0, ← map_mul, hs, map_neg, map_neg, map_natCast, map_natCast]
  rcases mul_self_eq_mul_self_iff.1 h1 with h | h
  · obtain ⟨ρ, e⟩ := tauE_surj' D φ h
    exact ⟨ρ, Or.inl e⟩
  · obtain ⟨ρ, e⟩ := tauE_surj' D (ComplexEmbedding.conjugate φ) (by
      rw [ComplexEmbedding.conjugate_coe_eq, h, map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal]; ring)
    exact ⟨ρ, Or.inr e⟩


end GlobalTheory.MassLink
