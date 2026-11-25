module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdMinorsMemInv
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.CBinet
public import Init.Core
public import Init.Data.Function
public import Init.Data.Nat.Lemmas
public import Init.Prelude
public import Init.PropLemmas
public import Init.SimpLemmas
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Fintype.Sets
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Logic.Embedding.Basic
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Fin.Basic
public import Mathlib.Order.Hom.Basic
public import Mathlib.Order.Lattice
public import Mathlib.Order.Monotone.Basic
public import Mathlib.Order.Monotone.Defs

@[expose] public section

open Classical

noncomputable section

namespace GlobalTheory.MinorFrame

open MvPolynomial

def smEquivSub (a d : ℕ) : {s : Fin a → Fin d // StrictMono s} ≃ {S : Finset (Fin d) // S.card = a} where
  toFun s := ⟨Finset.univ.map ⟨s.1, s.2.injective⟩, by simp⟩
  invFun S := ⟨S.1.orderEmbOfFin S.2, (S.1.orderEmbOfFin S.2).strictMono⟩
  left_inv s := by
    apply Subtype.ext
    symm
    exact Finset.orderEmbOfFin_unique _ (fun x => by simp) s.2
  right_inv S := by
    apply Subtype.ext
    simp only
    ext x
    simp only [Finset.mem_map, Finset.mem_univ, true_and, Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨y, rfl⟩; exact Finset.orderEmbOfFin_mem _ _ _
    · intro hx
      have : x ∈ Set.range (S.1.orderEmbOfFin S.2) := by rw [Finset.range_orderEmbOfFin]; exact hx
      exact this

theorem det_mul_eq_sum_sm {R : Type} [CommRing R] {a d : ℕ} (A : Matrix (Fin a) (Fin d) R)
    (B : Matrix (Fin d) (Fin a) R) :
    (A * B).det = ∑ s : {s : Fin a → Fin d // StrictMono s},
      (A.submatrix id s.1).det * (B.submatrix s.1 id).det := by
  rw [ReciprocityTheory.ChartRestriction.DS.S7.det_mul_eq_sum_submatrix, ← (smEquivSub a d).symm.sum_comp]
  rfl

end GlobalTheory.MinorFrame

noncomputable section
namespace GlobalTheory.MinorFrame
open MvPolynomial
open scoped Matrix
variable {ι : Type} [Fintype ι]

def xMat (τ : ι) (d a : ℕ) : Matrix (Fin d) (Fin a) (Pol ι d a) := Matrix.of fun i j => X (τ, i, j)

end GlobalTheory.MinorFrame

noncomputable section
namespace GlobalTheory.MinorFrame
open scoped Matrix

end GlobalTheory.MinorFrame

noncomputable section
namespace GlobalTheory.MinorFrame
open MvPolynomial
open scoped Matrix ComplexConjugate

variable {ι : Type} [Fintype ι]

end GlobalTheory.MinorFrame

noncomputable section
namespace GlobalTheory.MinorFrame
open MvPolynomial

end GlobalTheory.MinorFrame
