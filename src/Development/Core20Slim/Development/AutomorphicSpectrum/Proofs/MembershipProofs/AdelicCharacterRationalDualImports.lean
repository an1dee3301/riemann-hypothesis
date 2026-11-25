module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Notation.Indicator
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Valuation.ValuationSubring

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain

namespace GlobalTheory.CompanionTheory.ThetaUniq

def cosetInd (F : Type) [Field F] [NumberField F] {κ : Type} (N : ℕ) (d : κ → F) :
    (κ → FiniteAdeleRing (𝓞 F) F) → ℂ :=
  Set.indicator {x | ∀ i, ∃ u : FiniteAdeleRing (𝓞 F) F, (∀ v, u v ∈ v.adicCompletionIntegers F) ∧
    x i = algebraMap F (FiniteAdeleRing (𝓞 F) F) (d i) + N • u} 1

end GlobalTheory.CompanionTheory.ThetaUniq

end
