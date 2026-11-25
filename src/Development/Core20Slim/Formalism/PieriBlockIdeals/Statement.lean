module

public import Mathlib

@[expose] public section

noncomputable section

open Finset Polynomial

namespace Formalism.CohomologicalDescent

open Classical


def IlInd (l : ℕ) (xm xp mB : ℤ) : ℝ :=
  if ∃ y : ℤ, xm ≤ y ∧ y ≤ xp ∧ (l : ℤ) ∣ y - mB then 1 else 0

def d0 (l : ℕ) (D : ℤ) : ℕ := sInf {d : ℕ | 1 ≤ d ∧ (l : ℤ) ∣ D - (d : ℤ)}





def mwCount (l : ℕ) (b : ℤ) (t κ : ℕ) (U : Finset ℤ) : ℕ :=
  ((U.filter (fun u => u ∉ Finset.Icc b (b + t - 1))).filter
    (fun u => ∃ x ∈ Finset.Icc (b - κ) (b + t - 1 + κ), x ≡ u [ZMOD (l : ℤ)])).card




end Formalism.CohomologicalDescent
