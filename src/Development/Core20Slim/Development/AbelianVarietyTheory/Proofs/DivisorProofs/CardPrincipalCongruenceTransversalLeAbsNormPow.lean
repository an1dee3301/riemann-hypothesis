module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetVecEq
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.CongLevRelIndexLe
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemPrincipalCongruenceLevelSubgroupIffIntegralCo
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Function
public import Init.Data.Nat.Basic
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Order.Kleene
public import Mathlib.Algebra.Quotient
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Basic.ExistsUnique
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Sets
public import Mathlib.Data.Matrix.Mul
public import Mathlib.GroupTheory.Coset.Defs
public import Mathlib.GroupTheory.Index
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.SetTheory.Cardinal.Finite

@[expose] public section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

noncomputable section

theorem GlobalTheory.card_congRep_le : ∀ (D : D7) (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ≠ ⊥ → ∀ (a : ℕ) (R : Finset (GA D a)), (∀ r ∈ R, r ∈ intG D a) → (∀ k ∈ intG D a, ∃! r, r ∈ R ∧ CongOne D 𝔪 (r⁻¹ * k)) → R.card ≤ Ideal.absNorm 𝔪 ^ (a ^ 2) := by
  intro D 𝔪 h𝔪 a R hR huniq
  classical
  obtain ⟨hne, hle⟩ := GlobalTheory.congLev_relIndex_le D 𝔪 h𝔪 a
  let Q := intG D a ⧸ (congLev D 𝔪 a).subgroupOf (intG D a)
  haveI : Finite Q := Nat.finite_of_card_ne_zero hne
  let f : R → Q := fun r => QuotientGroup.mk (⟨(r : GA D a), hR r r.2⟩ : intG D a)
  have hf : Function.Injective f := by
    rintro ⟨r, hr⟩ ⟨r', hr'⟩ h
    have h1 := QuotientGroup.eq.1 h
    rw [Subgroup.mem_subgroupOf] at h1
    have h2 : r⁻¹ * r' ∈ congLev D 𝔪 a := h1
    have h3 := ((mem_congLev_iff D 𝔪 a _).1 h2).2
    have h4 : CongOne D 𝔪 (r'⁻¹ * r') := by
      rw [inv_mul_cancel]; exact congOne_one 𝔪 a
    obtain ⟨s, -, hs⟩ := huniq r' (hR r' hr')
    have e1 := hs r ⟨hr, h3⟩
    have e2 := hs r' ⟨hr', h4⟩
    exact Subtype.ext (e1.trans e2.symm)
  have hc := Nat.card_le_card_of_injective f hf
  rw [Nat.card_eq_fintype_card, Fintype.card_coe] at hc
  calc R.card ≤ Nat.card Q := hc
    _ = (congLev D 𝔪 a).relIndex (intG D a) := rfl
    _ ≤ _ := hle

end
