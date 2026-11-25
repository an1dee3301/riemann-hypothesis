module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConjugateCmValueCharacterPermutedWeight
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LatticeNormTransport
public import Development.AbelianVarietyTheory.Definitions.Divisors.EntireEqOfHalfPlane
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsFinSetSplitPlacesCoprimeConductor
public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Init.Core
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Empty
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.CMField
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Ideal.Defs

@[expose] public section

open NumberField GlobalTheory.CMVal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_conjugate_cmValueCharacter_permuted_weight : ∀ {K E : Type} [Field K] [NumberField K] [Field E] [NumberField E] [IsCMField E] [Algebra K E] {I : Type} [Fintype I] (φK : K →+* ℂ) (φ : I → E →+* ℂ) (s : ℕ) (κ : I → ℕ) (𝔣 : Ideal (OF E)) (χ : HChar E) (σ : ℂ ≃+* ℂ), IsCMType φ → (∀ i, (φ i).comp (algebraMap K E) = φK) → (starRingEnd ℂ).comp φK ≠ φK → GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.Fixes φK σ → IsValChar φ s κ 𝔣 ∅ χ → ∃ (π : Equiv.Perm I) (χ' : HChar E), GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.IsConjWt φ σ κ (κ ∘ π) ∧ GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.IsConjChar φ s (κ ∘ π) σ χ χ' ∧ IsValChar φ s (κ ∘ π) 𝔣 ∅ χ' := by
  first | exact @GlobalTheory.ConjValChar.exists_conj_valChar | exact GlobalTheory.ConjValChar.exists_conj_valChar | (intros; apply GlobalTheory.ConjValChar.exists_conj_valChar <;> assumption)
