module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareStanding
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemPairLat
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.Algebra.CharP.IntermediateField
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Order.Group.Action
public import Mathlib.Algebra.Order.Kleene
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Ring.Action.Basic
public import Mathlib.Algebra.Ring.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.FieldTheory.Normal.Defs
public import Mathlib.FieldTheory.Perfect
public import Mathlib.FieldTheory.Separable
public import Mathlib.GroupTheory.OreLocalization.OreSet
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.CMField
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.Order.BoundedOrder.Basic
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.DedekindDomain.Different
public import Mathlib.RingTheory.DedekindDomain.Ideal.Basic
public import Mathlib.RingTheory.FractionalIdeal.Basic
public import Mathlib.RingTheory.FractionalIdeal.Inverse
public import Mathlib.RingTheory.FractionalIdeal.Operations
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Pointwise
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.RingTheory.OreLocalization.Ring
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open scoped nonZeroDivisors

namespace GlobalTheory

open scoped Pointwise

namespace StarAAbar

theorem star_eq_conj (D : D7) (x : D.host.E) : star x = D.host.conj x := by
  apply D.host.φ₀.injective
  letI := D.host.isCMField_hostE
  show D.host.φ₀ (IsCMField.complexConj D.host.E x) = _
  rw [NumberField.IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply]

theorem conj_conj (D : D7) (x : D.host.E) : D.host.conj (D.host.conj x) = x :=
  D.host.φ₀.injective (by
    rw [Formalism.HC.HostAx.conjE_apply, Formalism.HC.HostAx.conjE_apply, Complex.conj_conj])

theorem coe_smul {L : Type} [Field L] [NumberField L] (σ : Gal(L/ℚ)) (X : 𝓞 L) :
    ((σ • X : 𝓞 L) : L) = σ (X : L) := rfl

theorem bb_ne_bot {D : D7} : D.host.𝔟 ≠ ⊥ := by
  intro h
  have h1 := D.host.𝔟_spec.1
  rw [h] at h1
  simp only [Submodule.bot_mul] at h1
  exact differentIdeal_ne_bot h1

theorem conj_bb_ne_bot {D : D7} : D.host.conj • D.host.𝔟 ≠ ⊥ := by
  intro h
  apply bb_ne_bot (D := D)
  have := congrArg (fun I : Ideal (𝓞 D.host.E) => D.host.conj⁻¹ • I) h
  simpa using this

theorem conj_inv_smul {D : D7} (x : 𝓞 D.host.E) : D.host.conj⁻¹ • x = D.host.conj • x := by
  have h : D.host.conj⁻¹ = D.host.conj := by
    rw [inv_eq_iff_mul_eq_one]
    exact AlgEquiv.ext fun y => conj_conj D y
  rw [h]

end StarAAbar


set_option synthInstance.maxHeartbeats 160000 in
set_option maxHeartbeats 800000 in
theorem star_mem_AA_of_mem_AAbar : ∀ {D : D7} {c : D.host.E}, c ∈ D.host.AAbar → star c ∈ D.host.AA := by
  intro D c hc
  have hJ : ((D.host.𝔟 : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 StarAAbar.bb_ne_bot
  have hJc : ((D.host.conj • D.host.𝔟 : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 StarAAbar.conj_bb_ne_bot

  have h1 : ∀ y ∈ D.host.conj • D.host.𝔟, c * (y : D.host.E) ∈
      ((D.host.conj • D.host.ccE : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) := by
    intro y hy
    have hyJ : (y : D.host.E) ∈ ((D.host.conj • D.host.𝔟 : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) :=
      (FractionalIdeal.mem_coeIdeal _).2 ⟨y, hy, rfl⟩
    have := FractionalIdeal.mul_mem_mul hc hyJ
    unfold Host.AAbar at this
    rwa [mul_assoc, inv_mul_cancel₀ hJc, mul_one] at this

  have h2 : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) (star c) *
      ((D.host.𝔟 : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≤
      ((D.host.ccE : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) := by
    rw [FractionalIdeal.mul_le]
    intro i hi j hj
    obtain ⟨z, rfl⟩ := (FractionalIdeal.mem_spanSingleton _).1 hi
    obtain ⟨j', hj', rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hj
    have hy : D.host.conj • j' ∈ D.host.conj • D.host.𝔟 := Ideal.smul_mem_pointwise_smul _ _ _ hj'
    obtain ⟨x, hx, hxe⟩ := (FractionalIdeal.mem_coeIdeal _).1 (h1 _ hy)
    have hxs : D.host.conj • x ∈ D.host.ccE := by
      have := (Ideal.mem_pointwise_smul_iff_inv_smul_mem).1 hx
      rwa [StarAAbar.conj_inv_smul] at this
    have key : star c * algebraMap (𝓞 D.host.E) D.host.E j' = algebraMap (𝓞 D.host.E) D.host.E (D.host.conj • x) := by
      show star c * (j' : D.host.E) = ((D.host.conj • x : 𝓞 D.host.E) : D.host.E)
      rw [StarAAbar.coe_smul, show ((x : 𝓞 D.host.E) : D.host.E) = algebraMap (𝓞 D.host.E) D.host.E x from rfl, hxe,
        map_mul, StarAAbar.coe_smul, StarAAbar.conj_conj, StarAAbar.star_eq_conj]
    rw [smul_mul_assoc, key]
    exact Submodule.smul_mem _ _ ((FractionalIdeal.mem_coeIdeal _).2 ⟨_, hxs, rfl⟩)
  have h3 : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) (star c) ≤ D.host.AA := by
    unfold Host.AA Host.AA0
    calc FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) (star c)
        = FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) (star c) *
          ((D.host.𝔟 : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) *
          ((D.host.𝔟 : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)⁻¹ := by
          rw [mul_assoc, mul_inv_cancel₀ hJ, mul_one]
      _ ≤ _ := by gcongr
  exact h3 (FractionalIdeal.mem_spanSingleton_self _ _)

end GlobalTheory
