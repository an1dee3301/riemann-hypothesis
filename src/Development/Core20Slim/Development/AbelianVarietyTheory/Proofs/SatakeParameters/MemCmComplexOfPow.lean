module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.Bridge
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ClassPresBasic
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.SatakeParameters.HasRatBasisOfAct
public import Formalism.LocalToGlobal.Divisibility.ClassSum
public import Formalism.QuotientMetricDivisors.RatHermLcvTwist
public import Init.Core
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.PropLemmas
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.Hom.Rat
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.CharP.IntermediateField
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Units.Lemmas
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Rat
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Basic
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Finsupp.SMul
public import Mathlib.Data.Finsupp.SMulWithZero
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Rat.Defs
public import Mathlib.FieldTheory.AlgebraicClosure
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.FieldTheory.Perfect
public import Mathlib.FieldTheory.Separable
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.Order.Basic
public import Mathlib.Order.SetNotation
public import Mathlib.RingTheory.Algebraic.Basic
public import Mathlib.RingTheory.Algebraic.Defs
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal

@[expose] public section

open Formalism.IndefR.Bridge Formalism.L2.DIV Formalism.DivisionValues Formalism.L2.Col NumberField MeasureTheory Polynomial

noncomputable section

namespace GlobalTheory.PresRat

def conjAlg : algebraicClosure ℚ ℂ →+* algebraicClosure ℚ ℂ :=
  ((starRingEnd ℂ).comp (algebraicClosure ℚ ℂ).val.toRingHom).codRestrict (algebraicClosure ℚ ℂ) fun x => by
    have hx : IsAlgebraic ℚ (x : ℂ) := mem_algebraicClosure_iff.1 x.2
    exact mem_algebraicClosure_iff.2 (hx.algHom (starRingEnd ℂ).toRatAlgHom)

def cmComplex : Subfield ℂ :=
  (⨅ τ : algebraicClosure ℚ ℂ →+* ℂ, RingHom.eqLocusField (τ.comp conjAlg) ((starRingEnd ℂ).comp τ)).map
    (algebraicClosure ℚ ℂ).val.toRingHom

theorem mem_cmComplex {z : ℂ} : z ∈ cmComplex ↔ ∃ x : algebraicClosure ℚ ℂ, (x : ℂ) = z ∧
    ∀ τ : algebraicClosure ℚ ℂ →+* ℂ, τ (conjAlg x) = starRingEnd ℂ (τ x) := by
  unfold cmComplex
  rw [Subfield.mem_map]
  refine exists_congr fun x => ?_
  rw [Subfield.mem_iInf, and_comm]
  rfl

theorem conj_eq_inv_of_pow {z : ℂ} {n : ℕ} (hn : 0 < n) (hz : z ^ n = 1) : starRingEnd ℂ z = z⁻¹ :=
  (Complex.inv_eq_conj (Complex.norm_eq_one_of_pow_eq_one hz hn.ne')).symm

theorem mem_cmComplex_of_pow {z : ℂ} {n : ℕ} (hn : 0 < n) (hz : z ^ n = 1) : z ∈ cmComplex := by
  have ha : IsAlgebraic ℚ z := IsAlgebraic.of_pow hn (by rw [hz]; exact isAlgebraic_one)
  refine mem_cmComplex.2 ⟨⟨z, mem_algebraicClosure_iff.2 ha⟩, rfl, fun τ => ?_⟩
  set x : algebraicClosure ℚ ℂ := ⟨z, mem_algebraicClosure_iff.2 ha⟩
  have hx : x ^ n = 1 := Subtype.ext hz
  have h1 : conjAlg x = x⁻¹ := Subtype.ext (conj_eq_inv_of_pow hn hz)
  rw [h1, map_inv₀, conj_eq_inv_of_pow hn (by rw [← map_pow, hx, map_one])]

theorem mem_cmComplex_iff {K : Type} [Field K] [NumberField K] [StarRing K] (σ : K →+* ℂ)
    (hσ : ∀ a : K, σ (star a) = starRingEnd ℂ (σ a)) (a : K) : σ a ∈ cmComplex ↔ a ∈ cmMax K := by
  let s : K →+* algebraicClosure ℚ ℂ := σ.codRestrict (algebraicClosure ℚ ℂ) fun x =>
    mem_algebraicClosure_iff.2 ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).algHom σ.toRatAlgHom)
  have hs : conjAlg (s a) = s (star a) := Subtype.ext (hσ a).symm
  rw [mem_cmComplex]
  constructor
  · rintro ⟨x, hx, h⟩ φ
    have hx' : x = s a := Subtype.ext hx
    let _ : Algebra K (algebraicClosure ℚ ℂ) := s.toAlgebra
    have : Algebra.IsAlgebraic ℚ (algebraicClosure ℚ ℂ) := by
      convert algebraicClosure.isAlgebraic ℚ ℂ
    have : Algebra.IsAlgebraic K (algebraicClosure ℚ ℂ) :=
      Algebra.IsAlgebraic.tower_top (K := ℚ) K
    have h1 := h (ComplexEmbedding.lift (algebraicClosure ℚ ℂ) φ)
    rw [hx', hs] at h1
    have e : ∀ b, ComplexEmbedding.lift (algebraicClosure ℚ ℂ) φ (s b) = φ b := fun b =>
      ComplexEmbedding.lift_algebraMap_apply _ φ b
    rw [e, e] at h1
    exact h1
  · intro h
    exact ⟨s a, rfl, fun τ => by rw [hs]; exact h (τ.comp s)⟩

variable {G Γ W K : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W] [Field K]
  [NumberField K] [StarRing K] {ι : Γ →* G} {S : CSD K} {σ : K →+* ℂ} {ρ : Γ →* Module.End ℂ W}
  {J : Subgroup G} {χ : J →* ℂˣ} (P : ClassPres ι S σ ρ J χ)

theorem act_mem (hσ : ∀ a : K, σ (star a) = starRingEnd ℂ (σ a)) (hχ : ∀ k, ∃ n : ℕ, 0 < n ∧ χ k ^ n = 1)
    (hρ : ∀ γ j, ∃ c : S.ιV → K, (∀ i, c i ∈ cmMax K) ∧ ρ γ (P.coef (S.bV j)) = ∑ i, σ (c i) • P.coef (S.bV i))
    (k : J) (γ : Γ) (x : S.V) (hx : ∀ i, S.bV.repr x i ∈ cmMax K) (i : S.ιV) :
    (PresBasic.bW P).repr ((χ k : ℂ) • ρ γ (P.coef x)) i ∈ cmComplex := by
  obtain ⟨n, hn, hk⟩ := hχ k
  have h1 : (χ k : ℂ) ∈ cmComplex :=
    mem_cmComplex_of_pow hn (by rw [← Units.val_pow_eq_pow_val, hk, Units.val_one])
  have h2 : P.coef x = ∑ j, σ (S.bV.repr x j) • P.coef (S.bV j) := by
    conv_lhs => rw [← S.bV.sum_repr x]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [map_smulₛₗ]
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul, h2]
  refine cmComplex.mul_mem h1 ?_
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul]
  refine cmComplex.sum_mem fun j _ => cmComplex.mul_mem ((mem_cmComplex_iff σ hσ _).2 (hx j)) ?_
  obtain ⟨c, hc, e⟩ := hρ γ j
  rw [e]
  simp only [← PresBasic.bW_apply]
  rw [Module.Basis.repr_sum_self]
  exact (mem_cmComplex_iff σ hσ _).2 (hc i)

end GlobalTheory.PresRat

namespace GlobalTheory


end GlobalTheory
