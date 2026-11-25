module

public import Mathlib
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Function
public import Init.Data.Nat.Coprime
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Quotient
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Rat.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.FieldTheory.Separable
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.CMField
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.IntegralClosure.Algebra.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.UnitaryDetClass

open NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

section Lattices

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def IsUnitary (γ : Matrix (Fin n) (Fin n) E) : Prop :=
  (γ.map (IsCMField.complexConj E)).transpose * γ = 1


def CongrAt (Q : ℕ) (u v : Fin n → E) : Prop :=
  ∃ k : ℕ, Nat.Coprime k Q ∧ ∀ j, ∃ s : 𝓞 E, (k : E) * (u j - v j) = (Q : E) * (s : E)

abbrev StdMod (E : Type) [Field E] [NumberField E] (n Q : ℕ) : Type :=
  Fin n → 𝓞 E ⧸ Ideal.span {(Q : 𝓞 E)}

def IsMarking (Q : ℕ) (Λ : GenLat E n) (κ : Λ.La →ₗ[𝓞 E] StdMod E n Q) : Prop :=
  Function.Surjective κ ∧
  (∀ v : Λ.La, κ v = 0 ↔ ∃ u : Λ.La, v = Q • u) ∧
  ∀ (v w : Λ.La) (x y : Fin n → 𝓞 E),
    (∀ j, κ v j = Ideal.Quotient.mk _ (x j)) → (∀ j, κ w j = Ideal.Quotient.mk _ (y j)) →
      ∃ s : 𝓞 E, ∑ j, IsCMField.complexConj E ((v : Fin n → E) j) * (w : Fin n → E) j -
        ∑ j, IsCMField.complexConj E (x j : E) * (y j : E) = (Q : E) * (s : E)

end Lattices

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l)




end GlobalTheory.IndefiniteRowSideFullHecke.UnitaryDetClass
