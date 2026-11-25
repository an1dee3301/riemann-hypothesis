module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FrameLats

@[expose] public section

noncomputable section

open NumberField Matrix GlobalTheory.SgAlg
open scoped nonZeroDivisors

namespace GlobalTheory.SgGlob

variable {E : Type} [Field E] [NumberField E]








def UO (E : Type) [Field E] [NumberField E] (r : ℕ) : Set (Matrix (Fin (r + 1)) (Fin (r + 1)) E) :=
  {u | IsUp u ∧ ∀ a b : Fin (r + 1), a < b → u a b ∈ dInv E ((b : ℕ) - a)}

section Basic

variable {σ : E →+* E} {n m r : ℕ} {J : Matrix (Fin n) (Fin n) E} {Jb : Matrix (Fin m) (Fin m) E}


















end Basic

section Iota

variable {σ : E →+* E} {n m r : ℕ} {J : Matrix (Fin n) (Fin n) E} {Jb : Matrix (Fin m) (Fin m) E}

end Iota

section Iso

variable {σ : E →+* E} {n m r : ℕ} {J : Matrix (Fin n) (Fin n) E} {Jb : Matrix (Fin m) (Fin m) E}







end Iso

section Unip

variable {n r : ℕ}

end Unip

section Examples

variable {σ : E →+* E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

end Examples

end GlobalTheory.SgGlob
