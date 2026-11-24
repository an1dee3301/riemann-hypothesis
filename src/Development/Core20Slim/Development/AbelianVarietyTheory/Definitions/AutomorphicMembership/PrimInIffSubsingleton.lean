module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.InFrameStabilizer
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DiagMemCongruencePairs
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FrameLats
public import Formalism.HermitianLattices.StatementMaj
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow

@[expose] public section

noncomputable section

open NumberField Matrix GlobalTheory.SgAlg GlobalTheory.SgGlob IsDedekindDomain
open scoped nonZeroDivisors

namespace GlobalTheory.IntTerm

variable {E : Type} [Field E]

section Defs






variable [NumberField E]

def IntFrame (σ : E →+* E) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E) (T : E)
    (Λ : Submodule (𝓞 E) (Fin n → E)) (P : Matrix (Fin n) (Fin (r + 1)) E) : Prop :=
  IsFrame σ J T P ∧ PrimIn (frameLat P) Λ

def Cong {n r : ℕ} (g : ℕ) (Λ : Submodule (𝓞 E) (Fin n → E)) (P P' : Matrix (Fin n) (Fin (r + 1)) E) : Prop :=
  frameLat ((g : E)⁻¹ • (P' - P)) ≤ Λ

def admitted (σ : E →+* E) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E) (T' : E) (g : ℕ)
    (Λ : Submodule (𝓞 E) (Fin n → E)) (P P' : Matrix (Fin n) (Fin (r + 1)) E) : Prop :=
  IntFrame σ J T' Λ P' ∧ ∃ u ∈ UO E r, Cong g Λ (P * u) P'

def NO (σ : E →+* E) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E) (Λ : Submodule (𝓞 E) (Fin n → E))
    (P : Matrix (Fin n) (Fin (r + 1)) E) : Set (Matrix (Fin n) (Fin n) E) :=
  {s | InN σ J P s ∧ latMap s Λ = Λ}

def Move (σ : E →+* E) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E) (Λ : Submodule (𝓞 E) (Fin n → E))
    (P A B : Matrix (Fin n) (Fin (r + 1)) E) : Prop :=
  ∃ s ∈ NO σ J Λ P, ∃ u ∈ UO E r, B = s * A * u

end Defs

section Field

variable {σ : E →+* E} {n r : ℕ} {J s Y : Matrix (Fin n) (Fin n) E} {P P' : Matrix (Fin n) (Fin (r + 1)) E}
  {u v A Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E}

end Field

section Lattice

variable [NumberField E] {σ : E →+* E} {n r g : ℕ} {J s : Matrix (Fin n) (Fin n) E}
  {P P' A B C : Matrix (Fin n) (Fin (r + 1)) E} {u v : Matrix (Fin (r + 1)) (Fin (r + 1)) E}
  {Λ Λ' Λ'' M : Submodule (𝓞 E) (Fin n → E)} {T T' : E}

end Lattice

end GlobalTheory.IntTerm
