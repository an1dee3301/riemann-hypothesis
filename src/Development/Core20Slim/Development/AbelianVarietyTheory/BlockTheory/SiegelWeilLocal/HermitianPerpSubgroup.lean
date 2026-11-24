module

public import Mathlib
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.LocalToGlobal.Columns.GenericUnipotentCharacter
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FrameLats
public import Init.Data.Cast
public import Init.Data.Rat.Basic
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.SetTheory.Cardinal.Finite

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix
open scoped TensorProduct ENNReal Pointwise
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace GlobalTheory.IndefiniteRowSideFullHecke.FlagUnipotentStabilizers

section Unip

variable {A : Type} [CommRing A] {n : ℕ}



end Unip

section Groups

variable {F E : Type} [Field F] [Field E] [Algebra F E]
variable (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {n r : ℕ}
  (J : Matrix (Fin n) (Fin n) E)

end Groups

section Lattices

variable {E : Type} [Field E] [NumberField E] {n r : ℕ}

def SplitsCompletely (E : Type) [Field E] [NumberField E] (p : ℕ) : Prop :=
  Nat.card {w : HeightOneSpectrum (𝓞 E) // (p : 𝓞 E) ∈ w.asIdeal} = Module.finrank ℚ E


end Lattices

section Levels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable (σ : E →ₐ[F] E) {n r k : ℕ} (J : Matrix (Fin n) (Fin n) E)


variable (P : Matrix (Fin n) (Fin (r + 1)) E) (f : Matrix (Fin n) (Fin r) E)
  (L : Submodule (𝓞 E) (Fin n → E)) (SG : Finset (HeightOneSpectrum (𝓞 E)))
  (ε : HeightOneSpectrum (𝓞 E) → Fin k → Fin n → E)

end Levels

end GlobalTheory.IndefiniteRowSideFullHecke.FlagUnipotentStabilizers
