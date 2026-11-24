module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSBArgs
public import Batteries.Logic
public import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Init.ByCases
public import Init.Classical
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Int.Lemmas
public import Init.Data.Int.Order
public import Init.Data.List.Basic
public import Init.Data.Zero
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Action.Units
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Invertible.Basic
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Pi
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.GroupWithZero.Units.Lemmas
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Pointwise
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.IsBotOne
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Monoid.Unbundled.Pow
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Pi
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Attach
public import Mathlib.Data.Finset.Dedup
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.GroupTheory.ArchimedeanDensely
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Logic.Function.DependsOn
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Lattice
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Order.Nat
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.RingTheory.Valuation.Integers
public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
public import Mathlib.Tactic.FieldSimp.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Defs.Basic

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory ValuativeRel
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV

namespace GlobalTheory.MovedBound

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_le_inv_pow {ϖ : kˣ} (hϖ : IsUnif ϖ) (x : k) :
    ∃ n : ℕ, valuation k x ≤ (valuation k (ϖ : k) ^ n)⁻¹ := by
  have h1 : valuation k (ϖ : k) < 1 := hϖ ▸ uniformizer_lt_one
  by_cases hx : x = 0
  · exact ⟨0, by simp [hx]⟩
  have hv : (valuation k x)⁻¹ ≠ 0 := by simp [hx]
  obtain ⟨m, hm⟩ := exists_pow_lt₀ h1 (Units.mk0 _ hv)
  have hu : 0 < valuation k (ϖ : k) ^ m := by
    rw [pos_iff_ne_zero]; simp
  refine ⟨m, ?_⟩
  have hx0 : 0 < valuation k x := by rw [pos_iff_ne_zero]; simp [hx]
  exact (le_inv_comm₀ hu hx0).1 (by simpa using hm.le)

theorem inv_pow_mono {ϖ : kˣ} (hϖ : IsUnif ϖ) {n N : ℕ} (h : n ≤ N) :
    (valuation k (ϖ : k) ^ n)⁻¹ ≤ (valuation k (ϖ : k) ^ N)⁻¹ := by
  have h1 : valuation k (ϖ : k) < 1 := hϖ ▸ uniformizer_lt_one
  have hu : 0 < valuation k (ϖ : k) ^ N := by rw [pos_iff_ne_zero]; simp
  exact inv_anti₀ hu (pow_le_pow_right_of_le_one' h1.le h)

theorem exists_uniform {α : Type*} (s : Finset α) (P : α → ℕ → Prop)
    (hP : ∀ a n N, n ≤ N → P a n → P a N) (h : ∀ a ∈ s, ∃ n, P a n) : ∃ n, ∀ a ∈ s, P a n := by
  classical
  choose f hf using h
  exact ⟨s.attach.sup fun a => f a.1 a.2, fun a ha =>
    hP _ _ _ (Finset.le_sup (f := fun a : s => f a.1 a.2) (Finset.mem_attach s ⟨a, ha⟩)) (hf a ha)⟩

theorem exists_matrix_bound {ϖ : kˣ} (hϖ : IsUnif ϖ) {m n : Type*} [Fintype m] [Fintype n] (P : Matrix m n k) :
    ∃ N : ℕ, ∀ r s, valuation k (P r s) ≤ (valuation k (ϖ : k) ^ N)⁻¹ := by
  obtain ⟨N, hN⟩ := exists_uniform (Finset.univ : Finset (m × n))
    (fun rs N => valuation k (P rs.1 rs.2) ≤ (valuation k (ϖ : k) ^ N)⁻¹)
    (fun _ _ _ h h' => h'.trans (inv_pow_mono hϖ h)) (fun rs _ => exists_le_inv_pow hϖ _)
  exact ⟨N, fun r s => hN (r, s) (Finset.mem_univ _)⟩

theorem val_mul_mul_le {a b c d : Type*} [Fintype b] [Fintype c] (P : Matrix a b k) (X : Matrix b c k)
    (Q : Matrix c d k) (p x q : ValueGroupWithZero k) (hP : ∀ r s, valuation k (P r s) ≤ p)
    (hX : ∀ r s, valuation k (X r s) ≤ x) (hQ : ∀ r s, valuation k (Q r s) ≤ q) (r : a) (s : d) :
    valuation k ((P * X * Q) r s) ≤ p * x * q := by
  rw [Matrix.mul_apply]
  refine Valuation.map_sum_le _ fun j _ => ?_
  rw [map_mul, Matrix.mul_apply]
  refine mul_le_mul' (Valuation.map_sum_le _ fun i _ => ?_) (hQ _ _)
  rw [map_mul]
  exact mul_le_mul' (hP _ _) (hX _ _)

end GlobalTheory.MovedBound

namespace GlobalTheory.MovedBound

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem val_unitsPow_inv (ϖ : kˣ) (n : ℕ) :
    valuation k (((ϖ ^ n)⁻¹ : kˣ) : k) = (valuation k (ϖ : k) ^ n)⁻¹ := by
  simp [Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, map_inv₀, map_pow]

theorem val_unitsPow (ϖ : kˣ) (n : ℕ) :
    valuation k ((ϖ ^ n : kˣ) : k) = valuation k (ϖ : k) ^ n := by
  simp [Units.val_pow_eq_pow_val, map_pow]

end GlobalTheory.MovedBound


open GlobalTheory.MovedBound in
theorem GlobalTheory.MovedBound.moved_bounded_locConst : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (G : Grid k) (ϖ : kˣ) (e : ℕ) (T : G.Args → ℂ) (keep : Bool) (g : G.VertexGroup), IsUnif ϖ → G.IsTensor ϖ e (oppositePath G.m) T → ∃ n : ℕ, (∀ z : G.Args, moved G keep g T z ≠ 0 → ∀ b ∈ oppositePath G.m, ∀ r s, valuation k (z b r s) ≤ valuation k (((ϖ ^ n)⁻¹ : kˣ) : k)) ∧ ∀ z δ : G.Args, (∀ b ∈ oppositePath G.m, ∀ r s, valuation k (δ b r s) ≤ valuation k ((ϖ ^ n : kˣ) : k)) → moved G keep g T (z + δ) = moved G keep g T z := by
  intro k _ _ _ _ G ϖ e T keep g hϖ hT
  classical
  set u := valuation k (ϖ : k) with hu_def
  have hu0 : u ≠ 0 := by simp [u]
  have hu1 : u ≤ 1 := (hϖ ▸ uniformizer_lt_one).le
  let A : ∀ b : Edge, Matrix (Fin (G.rank b.tgt)) (Fin (G.rank b.tgt)) k := fun b => ((Assignment.one.read (g b.tgt))⁻¹).val
  let Ai : ∀ b : Edge, Matrix (Fin (G.rank b.tgt)) (Fin (G.rank b.tgt)) k := fun b => (Assignment.one.read (g b.tgt)).val
  let B : ∀ b : Edge, Matrix (Fin (G.rank b.src)) (Fin (G.rank b.src)) k := fun b => (Assignment.one.read (g b.src)).val
  let Bi : ∀ b : Edge, Matrix (Fin (G.rank b.src)) (Fin (G.rank b.src)) k := fun b => ((Assignment.one.read (g b.src))⁻¹).val
  obtain ⟨n0, hn0⟩ := exists_uniform (oppositePath G.m).toFinset
    (fun b N => (∀ r s, valuation k (A b r s) ≤ (u ^ N)⁻¹) ∧ (∀ r s, valuation k (Ai b r s) ≤ (u ^ N)⁻¹) ∧
      (∀ r s, valuation k (B b r s) ≤ (u ^ N)⁻¹) ∧ (∀ r s, valuation k (Bi b r s) ≤ (u ^ N)⁻¹))
    (fun _ _ _ h ⟨h1, h2, h3, h4⟩ => ⟨fun r s => (h1 r s).trans (inv_pow_mono hϖ h),
      fun r s => (h2 r s).trans (inv_pow_mono hϖ h), fun r s => (h3 r s).trans (inv_pow_mono hϖ h),
      fun r s => (h4 r s).trans (inv_pow_mono hϖ h)⟩)
    (fun b _ => by
      obtain ⟨n1, h1⟩ := exists_matrix_bound hϖ (A b)
      obtain ⟨n2, h2⟩ := exists_matrix_bound hϖ (Ai b)
      obtain ⟨n3, h3⟩ := exists_matrix_bound hϖ (B b)
      obtain ⟨n4, h4⟩ := exists_matrix_bound hϖ (Bi b)
      refine ⟨n1 + n2 + n3 + n4, fun r s => (h1 r s).trans (inv_pow_mono hϖ (by omega)),
        fun r s => (h2 r s).trans (inv_pow_mono hϖ (by omega)), fun r s => (h3 r s).trans (inv_pow_mono hϖ (by omega)),
        fun r s => (h4 r s).trans (inv_pow_mono hϖ (by omega))⟩)
  have hmv : ∀ x : G.Args, ∀ b, G.moveArgs .one g x b = A b * x b * B b := fun _ _ => rfl
  refine ⟨2 * n0 + e, ?_, ?_⟩
  · intro z hz b hb r s
    have hT0 : T (G.moveArgs .one g z) ≠ 0 := by
      intro h0; apply hz; simp [moved, Grid.pathAct, h0]
    have hint : G.moveArgs .one g z b ∈ matLat _ (stdLat k _) := by
      by_contra hc; exact hT0 (hT.2.1 _ b hb hc)
    have hint' := mem_matLat_stdLat.1 hint
    have hz' : z b = Ai b * G.moveArgs .one g z b * Bi b := by
      simp [hmv, A, Ai, B, Bi, ← Matrix.mul_assoc]
    obtain ⟨-, h2, -, h4⟩ := hn0 b (List.mem_toFinset.2 hb)
    rw [hz', val_unitsPow_inv]
    refine (val_mul_mul_le _ _ _ _ 1 _ h2 (fun r s => (hint' r s)) h4 r s).trans ?_
    rw [mul_one, ← mul_inv, ← pow_add]
    exact inv_pow_mono hϖ (by omega)
  · intro z δ hδ
    let δ' : G.Args := fun b => if b ∈ oppositePath G.m then G.moveArgs .one g δ b else 0
    have h1 : T (G.moveArgs .one g (z + δ)) = T (G.moveArgs .one g z + δ') := by
      refine hT.1 fun b hb => ?_
      simp only [Set.mem_setOf_eq] at hb
      simp [δ', hb, hmv, Matrix.mul_add, Matrix.add_mul]
    have h2 : T (G.moveArgs .one g z + δ') = T (G.moveArgs .one g z) := by
      refine hT.2.2 _ _ fun b => ?_
      by_cases hb : b ∈ oppositePath G.m
      · simp only [δ', hb, if_true]
        obtain ⟨h1, -, h3, -⟩ := hn0 b (List.mem_toFinset.2 hb)
        have hd : ∀ r s, valuation k (δ b r s) ≤ u ^ (2 * n0 + e) := fun r s => by
          rw [← val_unitsPow]; exact hδ b hb r s
        have hbd : ∀ r s, valuation k (G.moveArgs .one g δ b r s) ≤ u ^ e := fun r s => by
          rw [hmv]
          refine (val_mul_mul_le _ _ _ _ _ _ h1 hd h3 r s).trans (le_of_eq ?_)
          rw [show 2 * n0 + e = n0 + (n0 + e) by ring, pow_add, pow_add]
          field_simp
        rw [mem_matLat]
        intro i
        rw [mem_smul_lat, mem_stdLat]
        intro j
        rw [Valuation.mem_integer_iff]
        simp only [Units.smul_def, Pi.smul_apply, smul_eq_mul, Matrix.row_apply]
        rw [map_mul, val_unitsPow_inv]
        calc (u ^ e)⁻¹ * valuation k (G.moveArgs .one g δ b i j) ≤ (u ^ e)⁻¹ * u ^ e := mul_le_mul' le_rfl (hbd i j)
          _ = 1 := inv_mul_cancel₀ (pow_ne_zero _ hu0)
      · simp only [δ', hb, if_false]
        exact zero_mem _
    simp only [moved, Grid.pathAct, h1, h2]
