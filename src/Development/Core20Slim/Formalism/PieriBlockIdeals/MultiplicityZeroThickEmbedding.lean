module

public import Development.Core20Slim.Formalism.PieriBlockIdeals.LemmaWFromLattice
public import Development.Core20Slim.Formalism.PieriBlockIdeals.MertensReciprocalElementary

@[expose] public section

noncomputable section

open Finset

namespace Formalism.CohomologicalDescent.WorkedExample

open Formalism.CohomologicalDescent



structure Labels (ι : Type) (N : ℕ) where
  cc : ι → ι
  Φ : Set ι
  U : ι → Fin N → ℤ
  U' : ι → Fin N → ℤ
  bot : ι → ℤ

namespace Labels

variable {ι : Type} {N : ℕ}

def Refl (D : Labels ι N) (σ : Equiv.Perm ι) (h t : ℕ) : Prop :=
  (∀ i, D.cc (D.cc i) = i) ∧ (∀ i, σ (D.cc i) = D.cc (σ i)) ∧ (∀ i, i ∈ D.Φ ∨ D.cc i ∈ D.Φ) ∧
  (∀ i a, D.U (D.cc i) a = (h : ℤ) - D.U i (Fin.rev a)) ∧
  (∀ i a, D.U' (D.cc i) a = (h : ℤ) - D.U' i (Fin.rev a)) ∧
  (∀ i, D.bot (D.cc i) = (h : ℤ) - (D.bot i + (t : ℤ) - 1))

def Linked (D : Labels ι N) (F : Type) [Field F] (t : ℕ) (cst : ι → ℤ) : Prop :=
  ∀ i ∈ D.Φ, StrictAnti (D.U i) ∧ StrictAnti (D.U' i) ∧
    (∀ s : Fin t, ∃ a, D.U i a = D.bot i + ((s : ℕ) : ℤ)) ∧
    (∏ a, (Polynomial.X + Polynomial.C (((D.U i a + cst i : ℤ)) : F))) =
      ∏ a, (Polynomial.X + Polynomial.C (((D.U' i a + cst i : ℤ)) : F))

def Carried (D : Labels ι N) (ep : ι → ι) (J : ι → Fin N → ℤ) (botJ : ι → ℤ) : Prop :=
  (ep = id ∨ ep = D.cc) ∧ (∀ i, J (ep i) = D.U' i) ∧ (∀ i, botJ (ep i) = D.bot i)


end Labels






end Formalism.CohomologicalDescent.WorkedExample
