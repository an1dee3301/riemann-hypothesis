module

public import Mathlib
public import Formalism.FockGram.StatementFock

@[expose] public section

open MvPolynomial

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.CornerMinors

def nextPart {l : ℕ} (a : Fin l → ℕ) (i : Fin l) : ℕ :=
  if h : (i : ℕ) + 1 < l then a ⟨i + 1, h⟩ else 0

def topMinor {n l : ℕ} (h : l ≤ n) (i : Fin l) : MvPolynomial (Fin n × Fin l) ℂ :=
  (Matrix.of fun r c : Fin (i + 1) =>
    (X (⟨r, by have := r.2; have := i.2; omega⟩, ⟨c, by have := c.2; have := i.2; omega⟩) :
      MvPolynomial (Fin n × Fin l) ℂ)).det

def bottomMinor {n l : ℕ} (h : l ≤ n) (i : Fin l) : MvPolynomial (Fin n × Fin l) ℂ :=
  (Matrix.of fun r c : Fin (i + 1) =>
    (X (⟨n - (i + 1) + r, by have := r.2; have := i.2; omega⟩,
        ⟨c, by have := c.2; have := i.2; omega⟩) :
      MvPolynomial (Fin n × Fin l) ℂ)).det

def delTop {n l : ℕ} (h : l ≤ n) (a : Fin l → ℕ) : MvPolynomial (Fin n × Fin l) ℂ :=
  ∏ i : Fin l, topMinor h i ^ (a i - nextPart a i)

def delBottom {n l : ℕ} (h : l ≤ n) (a : Fin l → ℕ) : MvPolynomial (Fin n × Fin l) ℂ :=
  ∏ i : Fin l, bottomMinor h i ^ (a i - nextPart a i)

def hookDen {l : ℕ} (a : Fin l → ℕ) : ℚ :=
  ∏ i : Fin l, ∏ j ∈ Finset.Ioi i, ((a i : ℚ) - (a j : ℚ) + ((j : ℕ) : ℚ) - ((i : ℕ) : ℚ))

def hookProd {l : ℕ} (a : Fin l → ℕ) : ℚ :=
  (∏ i : Fin l, ((a i + (l - ((i : ℕ) + 1))).factorial : ℚ)) / hookDen a





end GlobalTheory.IndefiniteRowSideFullHecke.CornerMinors
