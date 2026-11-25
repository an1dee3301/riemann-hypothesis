module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NonemptyInvFunEquiv
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.MinorOrderedEntries
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsGanGrossPrasadRowWeights
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Fin.Basic
public import Init.Data.Int.Basic
public import Init.Data.Int.Lemmas
public import Init.Data.Int.Order
public import Init.Data.List.Basic
public import Init.Data.List.FinRange
public import Init.Data.List.Lemmas
public import Init.Data.List.Nat.Range
public import Init.Data.List.Pairwise
public import Init.Data.List.Range
public import Init.Data.Nat.Basic
public import Init.Data.Nat.Lemmas
public import Init.Data.NeZero
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.GetElem
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Prelude
public import Init.PropLemmas
public import Init.SimpLemmas
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Order.Group.Defs
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Order.IsBotOne
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
public import Mathlib.Algebra.Order.Ring.Cast
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Algebra.Order.Ring.Rat
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Ring.Unbundled.Rat
public import Mathlib.Algebra.Order.Star.Rat
public import Mathlib.Algebra.Order.SuccPred
public import Mathlib.Algebra.Order.ZeroLEOne
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Algebra.Star.Rat
public import Mathlib.Basic.IsEmpty.Defs
public import Mathlib.Data.Int.Cast.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Rat.Defs
public import Mathlib.Logic.Function.Defs
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Lattice
public import Mathlib.Order.Nat
public import Mathlib.Order.SuccPred.Nat
public import Mathlib.Tactic.CancelDenoms.Core
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries

namespace GlobalTheory.StrictInterlace

inductive Alt : ℚ → List ℚ → List ℚ → ℚ → Prop
  | nil (x : ℚ) : Alt x [] [] x
  | cons {x s b y : ℚ} {sm bg : List ℚ} : x > s → s > b → Alt b sm bg y → Alt x (s :: sm) (b :: bg) y

theorem Alt.append {x y z : ℚ} {s b s' b' : List ℚ} (h : Alt x s b y) (h' : Alt y s' b' z) :
    Alt x (s ++ s') (b ++ b') z := by
  induction h with
  | nil x => simpa using h'
  | cons h1 h2 _ ih => exact Alt.cons h1 h2 (ih h')

theorem Alt.interlace {x y : ℚ} {s b : List ℚ} (h : Alt x s b y) : Interlace (x :: b) s := by
  induction h with
  | nil x => exact ⟨rfl, fun i h => absurd h (by simp)⟩
  | cons h1 h2 _ ih =>
    refine ⟨by simpa using ih.1, fun i h h' => ?_⟩
    cases i with
    | zero => exact ⟨h1, h2⟩
    | succ i => exact ih.2 i (by simpa using h) (by simpa using h')

def Above (x : ℚ) (L : List ℚ) : Prop := ∀ z : ℤ, (z : ℚ) ∈ L → x > z

theorem alt_flatMap {ι : Type} (f g h : ι → List ℚ)
    (seg : ∀ i x L, (f i ++ L).Pairwise (· > ·) → Above x (f i ++ L) → ∃ y, Alt x (g i) (h i) y ∧ Above y L)
    (l : List ι) (L : List ℚ) : ∀ x, (l.flatMap f ++ L).Pairwise (· > ·) → Above x (l.flatMap f ++ L) →
      ∃ y, Alt x (l.flatMap g) (l.flatMap h) y ∧ Above y L := by
  induction l with
  | nil => intro x _ hx; exact ⟨x, Alt.nil x, by simpa using hx⟩
  | cons i l ih =>
    intro x hp hx
    rw [List.flatMap_cons, List.append_assoc] at hp hx
    obtain ⟨y, h1, h2⟩ := seg i x _ hp hx
    obtain ⟨z, h3, h4⟩ := ih y (List.pairwise_append.1 hp).2.1 h2
    exact ⟨z, by simpa only [List.flatMap_cons] using h1.append h3, h4⟩

theorem block_succ (c : ℚ) (n : ℕ) : block c (n + 1) = (c + n / 2) :: block (c - 1 / 2) n := by
  simp only [block, List.range_succ_eq_map, List.map_cons, List.map_map]
  congr 1
  · push_cast; ring
  · refine List.map_congr_left fun i _ => ?_
    simp only [Function.comp]
    push_cast; ring

theorem mem_block (c : ℚ) {n i : ℕ} (hi : i < n) {x : ℚ} (hx : x = c + ((n : ℚ) - 1) / 2 - i) : x ∈ block c n :=
  List.mem_map.2 ⟨i, List.mem_range.2 hi, hx.symm⟩

theorem alt_block_upper (n : ℕ) (a : ℚ) : ∀ c x : ℚ, x > c + n / 2 → c - n / 2 > a →
    Alt x (block c (n + 1)) (block c n ++ [a]) a := by
  induction n with
  | zero =>
    intro c x h1 h2
    rw [block_succ]
    exact Alt.cons h1 (by simpa using h2) (Alt.nil a)
  | succ n ih =>
    intro c x h1 h2
    rw [block_succ c (n + 1), block_succ c n]
    push_cast at h1 h2 ⊢
    exact Alt.cons h1 (by linarith) (ih _ _ (by linarith) (by linarith))

theorem alt_block_lower (n : ℕ) : ∀ c : ℚ, Alt (c + n / 2) (block c n) (block (c - 1 / 2) n) (c - n / 2) := by
  induction n with
  | zero => intro c; simpa [block] using Alt.nil c
  | succ n ih =>
    intro c
    rw [block_succ c n, block_succ (c - 1 / 2) n]
    have e : c - ((n + 1 : ℕ) : ℚ) / 2 = c - 1 / 2 - n / 2 := by push_cast; ring
    rw [e]
    refine Alt.cons ?_ (by linarith) (ih _)
    push_cast; linarith

theorem seg_upper (c : ℤ) (a : ℚ) {s : ℕ} (hs : Odd s) (x : ℚ) (L : List ℚ)
    (hp : (block c s ++ [a] ++ L).Pairwise (· > ·)) (hx : Above x (block c s ++ [a] ++ L)) :
    ∃ y, Alt x (block c s) (block c (s - 1) ++ [a]) y ∧ Above y L := by
  obtain ⟨r, rfl⟩ := hs
  obtain ⟨h1, -, h2⟩ := List.pairwise_append.1 hp
  refine ⟨a, alt_block_upper (2 * r) a c x ?_ ?_, fun z hz => h2 a (by simp) _ hz⟩
  · have := hx (c + r) (List.mem_append_left _ (List.mem_append_left _
      (mem_block (i := 0) _ (by omega) (by push_cast; ring))))
    push_cast at this ⊢; linarith
  · exact (List.pairwise_append.1 h1).2.2 _ (mem_block (i := 2 * r) _ (by omega) (by push_cast; ring)) a (by simp)

theorem seg_middle (v : ℤ) (u : ℚ) (x : ℚ) (L : List ℚ)
    (hp : ([(v : ℚ), u] ++ L).Pairwise (· > ·)) (hx : Above x ([(v : ℚ), u] ++ L)) :
    ∃ y, Alt x [(v : ℚ)] [u] y ∧ Above y L := by
  obtain ⟨h1, -, h2⟩ := List.pairwise_append.1 hp
  exact ⟨u, Alt.cons (hx v (by simp)) (by simpa using h1) (Alt.nil u), fun z hz => h2 u (by simp) _ hz⟩

theorem seg_lower (b e : ℤ) {t : ℕ} (ht : Odd t) (x : ℚ) (L : List ℚ)
    (hp : (((-b : ℚ) :: block (-e) t) ++ L).Pairwise (· > ·)) (hx : Above x (((-b : ℚ) :: block (-e) t) ++ L)) :
    ∃ y, Alt x ((-b : ℚ) :: block (-e) t) (block (-e) (t + 1)) y ∧ Above y L := by
  obtain ⟨r, rfl⟩ := ht
  obtain ⟨h1, -, h2⟩ := List.pairwise_append.1 hp
  rw [block_succ (-e) (2 * r + 1)]
  refine ⟨_, Alt.cons ?_ ?_ (alt_block_lower _ _), fun z hz => ?_⟩
  · have := hx (-b) (by simp)
    exact_mod_cast this
  · have h3 : (-b : ℚ) > ((-e + r : ℤ) : ℚ) :=
      (List.pairwise_cons.1 h1).1 _ (mem_block (i := 0) _ (by omega) (by push_cast; ring))
    have h4 : -e + r < -b := by exact_mod_cast h3
    have h5 : ((-e + r + 1 : ℤ) : ℚ) ≤ ((-b : ℤ) : ℚ) := by exact_mod_cast h4
    push_cast at h5 ⊢; linarith
  · have h3 : ((-e - r : ℤ) : ℚ) > z :=
      h2 _ (List.mem_cons_of_mem _ (mem_block (i := 2 * r) _ (by omega) (by push_cast; ring))) _ hz
    have h4 : z < -e - r := by exact_mod_cast h3
    have h5 : ((z + 1 : ℤ) : ℚ) ≤ ((-e - r : ℤ) : ℚ) := by exact_mod_cast h4
    push_cast at h5 ⊢; linarith

theorem interlace_big_small (S : Sizes) (Q : Entries S) (hQ : Q.Good) : Interlace Q.bigPar Q.smallPar := by
  have ho := hQ.order
  rw [Entries.orderList, List.cons_append, List.cons_append, List.append_assoc] at ho
  obtain ⟨h0, ho⟩ := List.pairwise_cons.1 ho
  obtain ⟨y1, a1, b1⟩ := alt_flatMap _ _ _ (fun i => seg_upper (Q.c i) (Q.a i.succ) S.s_odd) _ _ (Q.a 0) ho
    (fun z hz => h0 _ hz)
  have ho2 := (List.pairwise_append.1 ho).2.1
  obtain ⟨y2, a2, b2⟩ := alt_flatMap _ _ _ (fun i => seg_middle (Q.v i) (Q.u i)) _ _ y1 ho2 b1
  have ho3 := (List.pairwise_append.1 ho2).2.1
  obtain ⟨y3, a3, -⟩ := alt_flatMap _ _ _ (fun i => seg_lower (Q.b i) (Q.e i) S.t_odd) (List.finRange S.m) [] y2
    (by simpa only [List.append_nil] using ho3) (by simpa only [List.append_nil] using b2)
  have := (a1.append (a2.append a3)).interlace
  simpa only [Entries.bigPar, Entries.psiPar, Entries.smallPar, Entries.basePar, List.cons_append, List.append_assoc,
    List.map_eq_flatMap] using this

end GlobalTheory.StrictInterlace
