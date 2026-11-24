module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
public import Formalism.HermitianLattices.StatementLat
public import Formalism.HermitianLattices.StatementMaj
public import Init.Data.Int.Basic
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.FractionalIdeal.Basic
public import Mathlib.RingTheory.Ideal.Prime

@[expose] public section

open Module NumberField IsDedekindDomain
open scoped Matrix nonZeroDivisors

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.ScaledValuationFormula

open Formalism.DivisionValues Formalism.L2.Indef

variable {K : Type} [Field K] [NumberField K]

def primePow (w : HeightOneSpectrum (𝓞 K)) (n : ℤ) : Submodule (𝓞 K) K :=
  (((w.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^ n : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K)

def scaledAt {d : ℕ} (w : HeightOneSpectrum (𝓞 K)) (n : ℤ) (B : Submodule (𝓞 K) (Fin d → K)) :
    Submodule (𝓞 K) (Fin d → K) :=
  Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (Formalism.HermitianLatticesTheory.idealSmul (primePow w n) B)

variable [StarRing K] {Bs : DefBase K} {Df : DefSide Bs}


end GlobalTheory.IndefiniteRowSideFullHecke.ScaledValuationFormula
