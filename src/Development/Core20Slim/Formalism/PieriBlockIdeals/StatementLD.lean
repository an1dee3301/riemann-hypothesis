module

public import Formalism.GradedWeylDivisibility.StatementA

@[expose] public section

open MvPolynomial

namespace Formalism.CohomologicalDescent.LD

open Formalism.GradedWeylDivisibility

def boxesOfContent {q : ℕ} (lam2 tau : Fin q → ℕ) (c : ℤ) : ℕ :=
  (Finset.univ.filter fun a : Fin q => (lam2 a : ℤ) ≤ c + (a.val : ℤ) ∧ c + (a.val : ℤ) < (tau a : ℤ)).card

def colLen {q : ℕ} (lam2 tau : Fin q → ℕ) (j : ℕ) : ℕ :=
  (Finset.univ.filter fun a : Fin q => lam2 a ≤ j ∧ j < tau a).card

def shapes (p w i : ℕ) {q : ℕ} (lam2 : Fin q → ℕ) : Finset (Fin q → ℕ) :=
  (Fintype.piFinset fun a : Fin q => Finset.Icc (lam2 a) (lam2 a + i)).filter fun tau =>
    (∀ a b : Fin q, a ≤ b → tau b ≤ tau a) ∧ ∑ a, tau a = ∑ a, lam2 a + i ∧
      (∀ b : Fin q, ∀ j < tau b, colLen lam2 tau j ≤ p) ∧ boxesOfContent lam2 tau (w : ℤ) = 0

def mu (p w i : ℕ) {q : ℕ} (lam2 : Fin q → ℕ) (c : ℤ) : ℕ :=
  (shapes p w i lam2).sup fun tau => boxesOfContent lam2 tau c

def Dn (p w i : ℕ) {q : ℕ} (lam2 : Fin q → ℕ) : ℤ :=
  ∏ k ∈ Finset.range (q + w + i), ((w : ℤ) - ((k : ℤ) - (q : ℤ))) ^ mu p w i lam2 ((k : ℤ) - (q : ℤ))

noncomputable def nablaWt (r : ℕ) (ν μ : Fin r → ℕ) : Submodule ℤ (MvPolynomial (Fin r × Fin r) ℤ) :=
  dualWeyl ℤ r r ν ⊓ weightedHomogeneousSubmodule ℤ (rowW r r) μ

def KilledAt (l r : ℕ) (ν μ : Fin r → ℕ) (c : ℤ) : Prop :=
  ∀ x ∈ nablaWt r ν μ, ∃ m : ℤ, ¬ (l : ℤ) ∣ m ∧ (m * c) • x ∈ weyl ℤ r r le_rfl ν

def ExpLe (l r : ℕ) (ν μ : Fin r → ℕ) (e : ℕ) : Prop := KilledAt l r ν μ ((l : ℤ) ^ e)


def blockWtLast (p q w : ℕ) (κ : Fin q → ℕ) : Fin (q + p) → ℕ := Fin.append κ (fun _ : Fin p => w)


def IsDepthLast (p q w : ℕ) (μ : Fin (q + p) → ℕ) (i : ℕ) : Prop :=
  ∑ a : Fin p, μ (Fin.natAdd q a) = p * w + i

def depth2 {r : ℕ} (ξ : Fin r → ℤ) (lam μ : Fin r → ℕ) : ℤ := ∑ a, ξ a * ((lam a : ℤ) - (μ a : ℤ))



def LemmaDLast : Prop :=
  ∀ (l p q w M : ℕ) (lam2 : Fin q → ℕ), l.Prime → Antitone lam2 → (∀ b, w ≤ lam2 b ∧ lam2 b ≤ M) →
    ∀ eL : ℕ, (∀ μ2 : Fin q → ℕ, ExpLe l q lam2 μ2 eL) →
      ∀ (i : ℕ) (μ : Fin (q + p) → ℕ), IsDepthLast p q w μ i →
        ExpLe l (q + p) (blockWtLast p q w lam2) μ
          (eL + padicValInt l (Dn p (M - w) i fun b : Fin q => M - lam2 (Fin.rev b)))








end Formalism.CohomologicalDescent.LD
