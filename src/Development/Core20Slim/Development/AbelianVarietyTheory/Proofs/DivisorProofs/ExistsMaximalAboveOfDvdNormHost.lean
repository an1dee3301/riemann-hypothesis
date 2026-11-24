module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLocalComponentUnitaryMatrix
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryHeckeCharacterValues
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetVecEq
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Nat.Div.Basic
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.Divisibility.Basic
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Order.Kleene
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Maximal
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.Ideal.Span

@[expose] public section

open NumberField

namespace GlobalTheory.MaximalIdealDividingNorm

theorem exists_maximal_above_of_dvd_norm {K : Type*} [Field K] [NumberField K]
    (𝔪 : Ideal (𝓞 K)) {p : ℕ} (hp : p.Prime) (hd : p ∣ Ideal.absNorm 𝔪) :
    ∃ P : Ideal (𝓞 K), P.IsMaximal ∧ 𝔪 ≤ P ∧ (p : 𝓞 K) ∈ P := by
  obtain ⟨P, hmax, hunder, hdiv⟩ := Ideal.exists_isMaximal_dvd_of_dvd_absNorm' hp 𝔪 hd
  refine ⟨P, hmax, Ideal.le_of_dvd hdiv, ?_⟩
  have h1 : (p : ℤ) ∈ Ideal.under ℤ P := by
    rw [hunder]
    exact Ideal.mem_span_singleton_self _
  have h2 : algebraMap ℤ (𝓞 K) (p : ℤ) ∈ P := Ideal.mem_comap.mp h1
  rwa [map_natCast] at h2

theorem exists_maximal_above_of_dvd_norm_host (D : Formalism.BasicNotions.D7)
    (𝔪 : Ideal (𝓞 (Formalism.BasicNotions.D7.host D).E)) (_h𝔪 : 𝔪 ≠ ⊥)
    {p : ℕ} (hp : p.Prime) (hd : p ∣ Ideal.absNorm 𝔪) :
    ∃ P : Ideal (𝓞 (Formalism.BasicNotions.D7.host D).E),
      P.IsMaximal ∧ 𝔪 ≤ P ∧ (p : 𝓞 (Formalism.BasicNotions.D7.host D).E) ∈ P :=
  exists_maximal_above_of_dvd_norm 𝔪 hp hd

end GlobalTheory.MaximalIdealDividingNorm
