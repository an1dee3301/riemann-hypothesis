module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.FunJetApply
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.NoncompactGeneratorRaisesPfil
public import Formalism.RealPlaceAnalysis.StatementA
public import Formalism.RealPlaceAnalysis.StatementKT
public import Formalism.RealPlaceAnalysis.StatementU
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Fin.Package
public import Init.Data.Int.Basic
public import Init.Data.Int.Lemmas
public import Init.Data.Int.Order
public import Init.Data.List.Basic
public import Init.Data.List.Perm
public import Init.Data.Nat.Lemmas
public import Init.Data.Order.Lemmas
public import Init.Data.Order.PackageFactories
public import Init.Data.Prod
public import Init.Data.Zero
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Range
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Lp.WithLp
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Operator.LinearIsometry
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Fin.Basic

@[expose] public section

open Matrix MeasureTheory Filter Topology Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.SphJet
open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator

namespace GlobalTheory.SphJet

theorem jetRel_perm_of_vanish_prefix {V W : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] {n : ℕ} {ε : Fin n → Bool}
    {E : Fin n → Fin n → Module.End ℂ V} {Λ : Fin n → ℝ} {u : V} {j : W →ₗᵢ[ℂ] V}
    {B : List (Fin n × Fin n) → W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ} {m : ℕ} (hB : JetRel ε E Λ u j B)
    (h0 : ∀ l : List (Fin n × Fin n), l.length ≤ m → B l = 0) {l l' : List (Fin n × Fin n)} (h : l.Perm l') :
    ∀ l₁ : List (Fin n × Fin n), (l₁ ++ l).length = m + 1 → B (l₁ ++ l) = B (l₁ ++ l') := by
  induction h with
  | nil => intro l₁ _; rfl
  | cons p _ ih =>
    intro l₁ hl
    have := ih (l₁ ++ [p]) (by simpa using hl)
    simpa using this
  | swap p q l =>
    intro l₁ hl
    obtain ⟨a, b⟩ := q
    obtain ⟨c, d⟩ := p
    have h1 := hB.1 l₁ l a b c d
    have hlen : ∀ r : Fin n × Fin n, B (l₁ ++ r :: l) = 0 := by
      intro r
      apply h0
      simp only [List.length_append, List.length_cons] at hl ⊢
      omega
    rw [hlen, hlen, ite_self, ite_self, sub_zero] at h1
    exact sub_eq_zero.mp h1
  | trans h₁ _ ih₁ ih₂ =>
    intro l₁ hl
    rw [ih₁ l₁ hl, ih₂ l₁ (by rw [← hl]; simp [h₁.length_eq])]

theorem jetRel_perm_and_compact_vanish :
    ∀ (V W : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup W] [InnerProductSpace ℂ W] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (Λ : Fin n → ℝ) (u : V) (j : W →ₗᵢ[ℂ] V) (B : List (Fin n × Fin n) → W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ) (m : ℕ), LowData ε E Λ u j → JetRel ε E Λ u j B → (∀ l : List (Fin n × Fin n), l.length ≤ m → B l = 0) → (∀ l l' : List (Fin n × Fin n), l.Perm l' → l.length = m + 1 → B l = B l') ∧ ∀ l : List (Fin n × Fin n), l.length = m + 1 → (∃ p ∈ l, ε p.1 = ε p.2) → B l = 0 := by
  intro V W _ _ _ _ n ε E Λ u j B m hL hB h0
  have hperm : ∀ l l' : List (Fin n × Fin n), l.Perm l' → l.length = m + 1 → B l = B l' := by
    intro l l' h hl
    simpa using jetRel_perm_of_vanish_prefix hB h0 h [] (by simpa using hl)
  refine ⟨hperm, ?_⟩
  rintro l hl ⟨⟨a, b⟩, hp, hab⟩
  classical
  have hpe := List.perm_cons_erase hp
  have hlen : (l.erase (a, b)).length ≤ m := by
    have := hpe.length_eq
    simp only [List.length_cons] at this
    omega
  rw [hperm _ _ hpe hl]
  ext y x
  have hy : j y ∈ Formalism.REAL.kSpan ε E u := by
    rw [← hL.2.2.2.2]; exact ⟨y, rfl⟩
  have hy2 : E b a (j y) ∈ Formalism.REAL.kSpan ε E u := compact_span_compact_stable ε E u b a hab.symm _ hy
  rw [← hL.2.2.2.2] at hy2
  obtain ⟨y', hy'⟩ := hy2
  rw [hB.2.2.1 _ a b hab y y' x hy', h0 _ hlen]
  simp

end GlobalTheory.SphJet
