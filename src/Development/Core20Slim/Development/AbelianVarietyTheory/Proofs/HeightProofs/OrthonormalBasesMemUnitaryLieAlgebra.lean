module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.HeightProofs.InnerDRepSq
public import Batteries.Classes.Order
public import Batteries.Data.List.Basic
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.HeightProofs.InvSqrtTwo
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Init.Classical
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.List.Basic
public import Init.Data.List.FinRange
public import Init.Data.List.Lemmas
public import Init.Data.Ord.Basic
public import Init.Data.Order.Ord
public import Init.Data.RArray
public import Init.Data.Zero
public import Init.Grind.Lemmas
public import Init.Grind.Norm
public import Init.Grind.Ring.Basic
public import Init.Grind.Ring.CommSolver
public import Init.Grind.Ring.Field
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Field.Basic
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Bool.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder

@[expose] public section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum GlobalTheory.TypeSum.CasBasis GlobalTheory.LowTypeDetermined
open scoped InnerProductSpace

noncomputable section
namespace GlobalTheory.TypeSum.CasBasis
variable {n : ℕ} {ε : Fin n → Bool}

theorem mem_lieSet_iff_entry {X : Mx n} : X ∈ lieSet ε ↔
    ∀ i j, star (X j i) * (if ε j then 1 else -1) + (if ε i then 1 else -1) * X i j = 0 := by
  simp only [lieSet, Set.mem_setOf_eq, inG, Jm]
  rw [← Matrix.ext_iff]
  simp [mul_diagonal, diagonal_mul, conjTranspose_apply]

theorem smul_unitE_diag_mem (a : Fin n) {c : ℂ} (hc : star c = -c) : c • unitE a a ∈ lieSet ε := by
  rw [mem_lieSet_iff_entry]
  intro i j
  simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, unitE, single_apply, smul_eq_mul, star_mul', hc,
    star_sub, star_add]
  split_ifs <;> simp only [star_one, star_zero] at * <;> grind

theorem smul_unitE_sub_mem_same {a b : Fin n} (h : ε a = ε b) {c : ℂ} (hc : star c = c) :
    c • (unitE a b - unitE b a) ∈ lieSet ε := by
  rw [mem_lieSet_iff_entry]
  intro i j
  simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, unitE, single_apply, smul_eq_mul, star_mul', hc,
    star_sub, star_add]
  split_ifs <;> simp only [star_one, star_zero] at * <;> grind

theorem smul_unitE_add_mem_same {a b : Fin n} (h : ε a = ε b) {c : ℂ} (hc : star c = -c) :
    c • (unitE a b + unitE b a) ∈ lieSet ε := by
  rw [mem_lieSet_iff_entry]
  intro i j
  simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, unitE, single_apply, smul_eq_mul, star_mul', hc,
    star_sub, star_add]
  split_ifs <;> simp only [star_one, star_zero] at * <;> grind

theorem smul_unitE_add_mem_opp {a b : Fin n} (h : ε a ≠ ε b) {c : ℂ} (hc : star c = c) :
    c • (unitE a b + unitE b a) ∈ lieSet ε := by
  rw [mem_lieSet_iff_entry]
  intro i j
  simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, unitE, single_apply, smul_eq_mul, star_mul', hc,
    star_sub, star_add]
  split_ifs <;> simp only [star_one, star_zero] at * <;> grind

theorem smul_unitE_sub_mem_opp {a b : Fin n} (h : ε a ≠ ε b) {c : ℂ} (hc : star c = -c) :
    c • (unitE a b - unitE b a) ∈ lieSet ε := by
  rw [mem_lieSet_iff_entry]
  intro i j
  simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, unitE, single_apply, smul_eq_mul, star_mul', hc,
    star_sub, star_add]
  split_ifs <;> simp only [star_one, star_zero] at * <;> grind

theorem star_invSqrtTwo : star invSqrtTwo = invSqrtTwo := by
  simp [invSqrtTwo]

theorem star_invSqrtTwo_mul_I : star (invSqrtTwo * Complex.I) = -(invSqrtTwo * Complex.I) := by
  simp [invSqrtTwo]

theorem kList_mem_lieSet {X : Mx n} (hX : X ∈ kList ε) : X ∈ lieSet ε := by
  simp only [kList, List.mem_append, List.mem_map, List.mem_flatMap, List.mem_cons, List.not_mem_nil,
    or_false] at hX
  rcases hX with ⟨a, -, rfl⟩ | ⟨p, hp, hX⟩
  · exact smul_unitE_diag_mem a (by simp [Complex.star_def])
  · have hs : ε p.1 = ε p.2 := by
      simp [pairs] at hp
      exact hp.2.2
    rcases hX with rfl | rfl
    · exact smul_unitE_sub_mem_same hs star_invSqrtTwo
    · exact smul_unitE_add_mem_same hs star_invSqrtTwo_mul_I

theorem pList_mem_lieSet {X : Mx n} (hX : X ∈ pList ε) : X ∈ lieSet ε := by
  simp only [pList, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hX
  obtain ⟨p, hp, hX⟩ := hX
  have hs : ε p.1 ≠ ε p.2 := by
    simp [pairs] at hp
    exact hp.2.2
  rcases hX with rfl | rfl
  · exact smul_unitE_add_mem_opp hs star_invSqrtTwo
  · exact smul_unitE_sub_mem_opp hs star_invSqrtTwo_mul_I

theorem bases_mem_lieSet : ∀ (n : ℕ) (ε : Fin n → Bool), (∀ i, kB ε i ∈ lieSet ε) ∧ ∀ b, pB ε b ∈ lieSet ε :=
  fun _ _ => ⟨fun i => kList_mem_lieSet (List.get_mem _ i), fun b => pList_mem_lieSet (List.get_mem _ b)⟩

end GlobalTheory.TypeSum.CasBasis
end
