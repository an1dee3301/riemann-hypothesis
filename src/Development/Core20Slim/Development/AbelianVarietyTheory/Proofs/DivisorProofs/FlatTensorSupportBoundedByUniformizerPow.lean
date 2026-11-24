module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSBArgs
public import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSum
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneCosetOfIsTensor
public import Init.BinderNameHint
public import Init.Classical
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Fin.Basic
public import Init.Data.Fin.Lemmas
public import Init.Data.Int.Basic
public import Init.Data.Int.Lemmas
public import Init.Data.Int.Order
public import Init.Data.List.Basic
public import Init.Data.List.Lemmas
public import Init.Data.List.Nat.Range
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Prelude
public import Init.PropLemmas
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Units
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Even
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Pi
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.GroupWithZero.Units.Lemmas
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Pointwise
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.IsBotOne
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Algebra.Ring.Pi
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.UnitBall
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Dedup
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Block
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.GroupTheory.ArchimedeanDensely
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Logic.Function.DependsOn
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
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
public import Mathlib.Tactic.Push
public import Mathlib.Topology.Defs.Basic

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory ValuativeRel
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV

noncomputable section

namespace GlobalTheory.FunObj.FlatSupp

open GlobalTheory.RootEx

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem val_inv_pow {ϖ : kˣ} (n : ℕ) :
    valuation k (((ϖ ^ n)⁻¹ : kˣ) : k) = (valuation k (ϖ : k) ^ n)⁻¹ := by
  rw [Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, map_inv₀, map_pow]

theorem val_inv_pow_mono {ϖ : kˣ} (hϖ : IsUnif ϖ) {n n' : ℕ} (h : n ≤ n') :
    valuation k (((ϖ ^ n)⁻¹ : kˣ) : k) ≤ valuation k (((ϖ ^ n')⁻¹ : kˣ) : k) := by
  rw [val_inv_pow, val_inv_pow]
  have h0 : valuation k (ϖ : k) ≠ 0 := by simp
  have h1 : valuation k (ϖ : k) ≤ 1 := hϖ ▸ uniformizer_lt_one.le
  exact inv_anti₀ (pow_pos (zero_lt_iff.2 h0) _) (pow_le_pow_of_le_one zero_le' h1 h)

theorem exists_le {ϖ : kˣ} (hϖ : IsUnif ϖ) (a : k) :
    ∃ n : ℕ, valuation k a ≤ valuation k (((ϖ ^ n)⁻¹ : kˣ) : k) := by
  by_cases ha : a = 0
  · exact ⟨0, by simp [ha]⟩
  have hv : valuation k a ≠ 0 := by simpa using ha
  obtain ⟨n, hn⟩ := exists_pow_lt₀ (hϖ ▸ uniformizer_lt_one : valuation k (ϖ : k) < 1) (Units.mk0 _ hv)⁻¹
  refine ⟨n, ?_⟩
  rw [val_inv_pow]
  have h0 : valuation k (ϖ : k) ≠ 0 := by simp
  simp only [Units.val_inv_eq_inv_val, Units.val_mk0] at hn
  have := le_of_lt hn
  rwa [le_inv_comm₀ (pow_pos (zero_lt_iff.2 h0) _) (zero_lt_iff.2 hv)] at this

theorem exists_bound_conj {ϖ : kˣ} (hϖ : IsUnif ϖ) {m n : Type} [Fintype m] [DecidableEq m] [Fintype n]
    [DecidableEq n] (A : GL m k) (B : GL n k) :
    ∃ N : ℕ, ∀ Z : Matrix m n k, (∀ r s, ((A⁻¹ : GL m k).val * Z * B.val) r s ∈ 𝒪[k]) →
      ∀ r s, valuation k (Z r s) ≤ valuation k (((ϖ ^ N)⁻¹ : kˣ) : k) := by
  classical
  choose nA hnA using fun p : m × m => exists_le hϖ (A.val p.1 p.2)
  choose nB hnB using fun p : n × n => exists_le hϖ ((B⁻¹ : GL n k).val p.1 p.2)
  set N0 := Finset.univ.sup nA ⊔ Finset.univ.sup nB
  have hc : valuation k (((ϖ ^ (N0 + N0))⁻¹ : kˣ) : k) =
      valuation k (((ϖ ^ N0)⁻¹ : kˣ) : k) * valuation k (((ϖ ^ N0)⁻¹ : kˣ) : k) := by
    rw [val_inv_pow, val_inv_pow, pow_add, mul_inv]
  set c := valuation k (((ϖ ^ N0)⁻¹ : kˣ) : k)
  have hA : ∀ r a, valuation k (A.val r a) ≤ c := fun r a =>
    (hnA (r, a)).trans (val_inv_pow_mono hϖ (le_sup_left.trans' (Finset.le_sup (f := nA) (Finset.mem_univ (r, a)))))
  have hB : ∀ b s, valuation k ((B⁻¹ : GL n k).val b s) ≤ c := fun b s =>
    (hnB (b, s)).trans (val_inv_pow_mono hϖ (le_sup_right.trans' (Finset.le_sup (f := nB) (Finset.mem_univ (b, s)))))
  refine ⟨N0 + N0, fun Z hZ r s => ?_⟩
  have hZ' : Z = A.val * ((A⁻¹ : GL m k).val * Z * B.val) * (B⁻¹ : GL n k).val := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one, ← Matrix.mul_assoc, Units.mul_inv,
      Matrix.one_mul]
  rw [hZ', hc]
  set W := (A⁻¹ : GL m k).val * Z * B.val
  simp only [Matrix.mul_apply]
  refine Valuation.map_sum_le _ fun b _ => ?_
  rw [map_mul]
  refine mul_le_mul' (Valuation.map_sum_le _ fun a _ => ?_) (hB b s)
  rw [map_mul]
  simpa using mul_le_mul' (hA r a) (show valuation k (W a b) ≤ 1 from hZ a b)


open Matrix in
theorem flatTensor_support : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (G : Grid k) (hs : 1 ≤ G.s) (ψ : AddChar k Circle) (ν : Measure k) (ϖ : kˣ) (e : ℕ) (T : G.Args → ℂ) (keep : Bool) (g : G.VertexGroup), IsUnif ϖ → G.IsTensor ϖ e (oppositePath G.m) T → ∃ n : ℕ, ∀ (x : ColArgs G) (y : RowArgs G), flatTensor hs ψ ν (moved G keep g T) x y ≠ 0 → (∀ j, j < G.m → ∀ r s, (j + 1 = G.m → r ≠ topLast G (j + 1)) → valuation k (x j r s) ≤ valuation k (((ϖ ^ n)⁻¹ : kˣ) : k)) ∧ ∀ i, i < G.m → ∀ r s, valuation k (y i r s) ≤ valuation k (((ϖ ^ n)⁻¹ : kˣ) : k) := by
  classical
  intro k _ _ _ _ _ _ G hs ψ ν ϖ e T keep g hϖ hT
  choose N hN using fun b : Edge => exists_bound_conj hϖ (Assignment.one.read (g b.tgt)) (Assignment.one.read (g b.src))
  refine ⟨(oppositePath G.m).toFinset.sup N, fun x y hne => ?_⟩
  obtain ⟨v, hv⟩ : ∃ v, flatIntegrand hs ψ (moved G keep g T) x y v ≠ 0 := by
    by_contra h
    push_neg at h
    apply hne
    unfold flatTensor
    simp [h]
  have hT0 : T (G.moveArgs .one g (fill hs x y v)) ≠ 0 := by
    intro h0
    apply hv
    simp [flatIntegrand, moved, Grid.pathAct, h0]
  have key : ∀ b ∈ oppositePath G.m, ∀ r s, valuation k (fill hs x y v b r s) ≤
      valuation k (((ϖ ^ (oppositePath G.m).toFinset.sup N)⁻¹ : kˣ) : k) := by
    intro b hb r s
    refine le_trans (hN b _ (fun r s => ?_) r s)
      (val_inv_pow_mono hϖ (Finset.le_sup (f := N) (List.mem_toFinset.2 hb)))
    have hm : (G.moveArgs .one g (fill hs x y v)) b ∈ matLat _ (GlobalTheory.SplitFlip.stdLat k _) := by
      by_contra h
      exact hT0 (hT.2.1 _ b hb h)
    exact mem_matLat_stdLat.1 hm r s
  refine ⟨fun j hj r s hr => ?_, fun i hi r s => ?_⟩
  · have hmem : Edge.theta G.m j ∈ oppositePath G.m := by simp [oppositePath]; omega
    by_cases hj' : j < G.m - 1
    · have h := key _ hmem (frame (b := G.rank (G.m, j)) (c := G.m - 2 - j + 1) (by have := topRank_add hs j; omega) (Sum.inl s))
        (frame (b := G.rank (G.m, j + 1)) (c := G.m - 2 - j) (by have := topRank_add hs (j + 1); omega) (Sum.inl r))
      rw [fill_theta, transpose_apply, downMap, dite_eq_left hj'] at h
      simpa [reindex_apply, submatrix_apply, Equiv.symm_apply_apply, stepPt, basePt, Free, Kept] using h
    · have hjm : j + 1 = G.m := by omega
      have hrk := topRank_add hs (j + 1)
      have hrk' := topRank_add hs j
      have hr' : r.val < G.rank (G.m, j + 1) := by
        have := hr hjm
        have h2 : (topLast G (j + 1)).val = topRank G (j + 1) - 1 := rfl
        rw [Ne, Fin.ext_iff, h2] at this
        have := r.2
        omega
      have h := key _ hmem (show Fin (G.rank (G.m, j)) from ⟨s.val, by have := s.2; omega⟩)
        (show Fin (G.rank (G.m, j + 1)) from ⟨r.val, hr'⟩)
      rw [fill_theta, transpose_apply, downMap, dite_eq_right hj', dite_eq_left hjm] at h
      simpa using h
  · have hmem : Edge.ex i G.m ∈ oppositePath G.m := by simp [oppositePath]; omega
    have h := key _ hmem s r
    rwa [fill_ex, transpose_apply] at h

end GlobalTheory.FunObj.FlatSupp
