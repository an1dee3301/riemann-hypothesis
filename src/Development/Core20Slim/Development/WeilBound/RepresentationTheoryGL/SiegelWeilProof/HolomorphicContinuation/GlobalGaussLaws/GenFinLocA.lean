module

public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocRedField
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
public import Formalism.SatakeDualWeyl.Statement
public import Init.Classical
public import Init.Core
public import Init.Data.Function
public import Init.Data.Int.Lemmas
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Block
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Maximal
public import Mathlib.RingTheory.Ideal.Span

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

open Matrix

namespace PositivityTheory.Rg.Sw.Glob.GenFinLocAH

variable {R S : Type} [CommRing R] [CommRing S] {n : ℕ}

def bf (M : Matrix (Fin (n + n)) (Fin (n + n)) R) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R :=
  M.submatrix finSumFinEquiv finSumFinEquiv

theorem bf_mul (M N : Matrix (Fin (n + n)) (Fin (n + n)) R) : bf (M * N) = bf M * bf N := by
  unfold bf; exact (Matrix.submatrix_mul_equiv M N _ _ _).symm

theorem block_matrix_to_fromBlocks (a b c d : Matrix (Fin n) (Fin n) R) : bf (GlobalTheory.StdUnn.blk4 a b c d) = fromBlocks a b c d := by
  unfold bf GlobalTheory.StdUnn.blk4; simp [Matrix.submatrix_submatrix]

theorem blkDm_eq (M : Matrix (Fin (n + n)) (Fin (n + n)) R) : blkDm M = (bf M).toBlocks₂₂ := rfl

theorem bf_map (f : R →+* S) (M : Matrix (Fin (n + n)) (Fin (n + n)) R) : bf (M.map f) = (bf M).map f := rfl

theorem bf_one : bf (1 : Matrix (Fin (n + n)) (Fin (n + n)) R) = 1 := Matrix.submatrix_one_equiv _

theorem bf_injective : Function.Injective (bf : Matrix (Fin (n + n)) (Fin (n + n)) R → _) := by
  intro M N h
  ext i j
  have := congrFun (congrFun h (finSumFinEquiv.symm i)) (finSumFinEquiv.symm j)
  simpa [bf] using this

theorem block_matrix_one : GlobalTheory.StdUnn.blk4 (1 : Matrix (Fin n) (Fin n) R) 0 0 1 = 1 :=
  bf_injective (by rw [block_matrix_to_fromBlocks, bf_one, fromBlocks_one])

theorem blkDm_map (f : R →+* S) (M : Matrix (Fin (n + n)) (Fin (n + n)) R) : (blkDm M).map f = blkDm (M.map f) := rfl

theorem det_map (f : R →+* S) (M : Matrix (Fin n) (Fin n) R) : f M.det = (M.map f).det := by
  rw [RingHom.map_det]; rfl

theorem block_matrix_map (f : R →+* S) (a b c d : Matrix (Fin n) (Fin n) R) :
    (GlobalTheory.StdUnn.blk4 a b c d).map f = GlobalTheory.StdUnn.blk4 (a.map f) (b.map f) (c.map f) (d.map f) :=
  bf_injective (by rw [bf_map, block_matrix_to_fromBlocks, block_matrix_to_fromBlocks, fromBlocks_map])

theorem eI_map (f : R →+* S) (I : Finset (Fin n)) : (eI I : Matrix (Fin n) (Fin n) R).map f = eI I := by
  ext i j; simp only [eI, map_apply, diagonal_apply]; split_ifs <;> simp

theorem wIm_map (f : R →+* S) (I : Finset (Fin n)) : (wIm I : Matrix (Fin (n + n)) (Fin (n + n)) R).map f = wIm I := by
  unfold wIm; rw [block_matrix_map]; simp [Matrix.map_sub, Matrix.map_one, Matrix.map_neg, eI_map]

theorem standard_symplectic_matrix_map (f : R →+* S) : (J2 R n).map f = J2 S n := by
  unfold J2; rw [block_matrix_map]; simp [Matrix.map_one, Matrix.map_neg]

theorem cT_map (σ : R →+* R) (σ' : S →+* S) (f : R →+* S) (hf : ∀ x, f (σ x) = σ' (f x)) {m p : Type}
    (M : Matrix m p R) : (Formalism.UG.cT σ M).map f = Formalism.UG.cT σ' (M.map f) := by
  ext i j; simp [Formalism.UG.cT, hf]

theorem isUnit_of (σ : R →+* R) (𝔪 : Ideal R) (horb : ∀ 𝔫 : Ideal R, 𝔫.IsMaximal → 𝔫 = 𝔪 ∨ 𝔫 = 𝔪.comap σ)
    (z : R) (h1 : z ∉ 𝔪) (h2 : σ z ∉ 𝔪) : IsUnit z := by
  by_contra hz
  obtain ⟨𝔫, h𝔫, hz𝔫⟩ := Ideal.exists_le_maximal (Ideal.span {z}) (by rwa [Ne, Ideal.span_singleton_eq_top])
  have hz' : z ∈ 𝔫 := hz𝔫 (Ideal.subset_span rfl)
  rcases horb 𝔫 h𝔫 with rfl | rfl
  · exact h1 hz'
  · exact h2 hz'

end PositivityTheory.Rg.Sw.Glob.GenFinLocAH
