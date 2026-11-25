module

public import Mathlib
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SumRhoEqTrace
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.StandardAdelicCharacterStatement
public import Batteries.Classes.RatCast
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
public import Init.Classical
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Notation.Pi.Basic
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Empty
public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Finsupp.SMul
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Int.Cast.Lemmas
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Rat.Cast.CharZero
public import Mathlib.Data.Rat.Cast.Defs
public import Mathlib.Data.Rat.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.Trace.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.ThW

open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups Kronecker

theorem Bf_mulVec_toA {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι] [DecidableEq ι]
    (B : Matrix ι ι F) (y : ι → F) : Bf B *ᵥ toA y = toA (B *ᵥ y) := by
  funext i
  exact (RingHom.map_mulVec (algebraMap F (A F)) B y i).symm

theorem trace_int_of_basis {F : Type} [Field F] [NumberField F]
    (b : Module.Basis (InfinitePlace F) ℤ (𝓞 F)) (N : ℕ) (c : F)
    (h : ∀ v, ∃ m : ℤ, (N : ℚ) * Algebra.trace ℚ F ((b v : F) * c) = m) (r : 𝓞 F) :
    ∃ n : ℤ, Algebra.trace ℚ F ((N : F) * c * (r : F)) = n := by
  choose m hm using h
  have hr : (r : F) = ∑ v, ((b.repr r v : ℤ) : F) * (b v : F) := by
    conv_lhs => rw [← b.sum_repr r]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum]
  refine ⟨∑ v, b.repr r v * m v, ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hr, Finset.mul_sum, map_sum]
  push_cast
  refine Finset.sum_congr rfl fun v _ => ?_
  have e : (N : F) * c * (((b.repr r v : ℤ) : F) * (b v : F)) =
      (((b.repr r v : ℤ) : ℚ) * (N : ℚ)) • ((b v : F) * c) := by
    rw [Algebra.smul_def]
    simp only [eq_ratCast, Rat.cast_mul, Rat.cast_intCast, Rat.cast_natCast]
    ring
  rw [e, map_smul, smul_eq_mul, mul_assoc, hm v]

theorem toA_mem_perp_latN_iff : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (A F) ℂ), IsStdChar F ψ → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (B : Matrix ι ι F) (b : Module.Basis (InfinitePlace F) ℤ (𝓞 F)) (N : ℕ), 0 < N → ∀ y : ι → F, toA y ∈ perp (chiB ψ (Bf B)) (latN F ι N : Set (ι → A F)) ↔ ∀ i v, ∃ m : ℤ, (N : ℚ) * Algebra.trace ℚ F ((b v : F) * (B *ᵥ y) i) = m := by
  intro F _ _ ψ hψ ι _ _ B b N _ y
  obtain ⟨-, hall⟩ := GlobalTheory.T.standard_adelic_character F
  obtain ⟨-, -, hchar⟩ := hall ψ hψ
  have hBy := Bf_mulVec_toA B y
  constructor
  · intro h i v
    have h1 : ∀ x ∈ Oh F, ψ (algebraMap F (A F) ((N : F) * (B *ᵥ y) i) * x) = 1 := by
      intro x hx
      have hmem : (Pi.single i ((N : A F) * x) : ι → A F) ∈ latN F ι N := by
        refine fun j => ?_
        by_cases hj : j = i
        · subst hj
          exact ⟨x, hx, by simp⟩
        · exact ⟨0, oh_zero, by simp [Pi.single_eq_of_ne hj]⟩
      have h2 : ψ ((Pi.single i ((N : A F) * x) : ι → A F) ⬝ᵥ (Bf B *ᵥ toA y)) = 1 := h _ hmem
      rw [hBy, single_dotProduct] at h2
      rw [← h2, map_mul (algebraMap F (A F)), map_natCast (algebraMap F (A F))]
      congr 1
      simp only [toA]
      ring
    obtain ⟨n, hn⟩ := (hchar _).mp h1 (b v)
    refine ⟨n, ?_⟩
    rw [← hn]
    have e : (N : F) * (B *ᵥ y) i * (b v : F) = (N : ℚ) • ((b v : F) * (B *ᵥ y) i) := by
      rw [Algebra.smul_def]
      push_cast
      ring
    rw [e, map_smul, smul_eq_mul]
  · intro h x hx
    have h1 : ∀ i, ∀ x ∈ Oh F, ψ (algebraMap F (A F) ((N : F) * (B *ᵥ y) i) * x) = 1 :=
      fun i => (hchar _).mpr (trace_int_of_basis b N _ (h i))
    show ψ (x ⬝ᵥ (Bf B *ᵥ toA y)) = 1
    rw [hBy, dotProduct]
    have h2 : ∀ s : Finset ι, ψ (∑ i ∈ s, x i * toA (B *ᵥ y) i) = 1 := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp
      | insert i s hi ih =>
        rw [Finset.sum_insert hi, AddChar.map_add_eq_mul, ih, mul_one]
        obtain ⟨x', hx', e⟩ := hx i
        rw [e, ← h1 i x' hx', map_mul (algebraMap F (A F)), map_natCast (algebraMap F (A F))]
        congr 1
        simp only [toA]
        ring
    exact h2 Finset.univ

end GlobalTheory.CompanionTheory.SW.ThW
