module

public import Mathlib
public import Init.Core
public import Init.Data.Nat.Basic
public import Init.Data.Sum.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Nat.Basic
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Order.Nat

@[expose] public section

@[reducible] noncomputable def UpperTheory.Reformulated.B.TotalDegreeLinear.PV :
    Type → Type → Type → Type :=
    fun (ι A B : Type) ↦ MvPolynomial (ι × A ⊕ ι × B) ℂ

noncomputable def UpperTheory.Reformulated.B.TotalDegreeLinear.sub :
    {ι A B : Type} → [Fintype ι] → Matrix ι ι ℂ → Matrix ι ι ℂ → UpperTheory.Reformulated.B.TotalDegreeLinear.PV ι A B →ₐ[ℂ] UpperTheory.Reformulated.B.TotalDegreeLinear.PV ι A B :=
    fun {ι A B : Type} [Fintype ι] (g h : Matrix ι ι ℂ) ↦
      MvPolynomial.aeval
        (Sum.elim
          (fun (x : ι × A) ↦
            ∑ j : ι, (MvPolynomial.C : ℂ → MvPolynomial (ι × A ⊕ ι × B) ℂ) (g x.1 j) * MvPolynomial.X (Sum.inl (j, x.2)))
          fun (y : ι × B) ↦
          ∑ j : ι, (MvPolynomial.C : ℂ → MvPolynomial (ι × A ⊕ ι × B) ℂ) (h y.1 j) * MvPolynomial.X (Sum.inr (j, y.2)))

private lemma UpperTheory.Reformulated.B.TotalDegreeLinear.totalDegree_aeval_le {σ τ : Type}
    (f : σ → MvPolynomial τ ℂ) (hf : ∀ i, (f i).totalDegree ≤ 1) (p : MvPolynomial σ ℂ) :
    (MvPolynomial.aeval f p).totalDegree ≤ p.totalDegree := by
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq]
  refine (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun d hd => ?_)
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  rw [MvPolynomial.algebraMap_eq, MvPolynomial.totalDegree_C, zero_add]
  refine (MvPolynomial.totalDegree_finsetProd _ _).trans ?_
  calc ∑ i ∈ d.support, (f i ^ d i).totalDegree
      ≤ ∑ i ∈ d.support, d i := Finset.sum_le_sum fun i _ =>
        (MvPolynomial.totalDegree_pow _ _).trans (by simpa using Nat.mul_le_mul_left (d i) (hf i))
    _ ≤ p.totalDegree := MvPolynomial.le_totalDegree hd

private lemma UpperTheory.Reformulated.B.TotalDegreeLinear.totalDegree_linear_le {ι τ : Type} [Fintype ι]
    (c : ι → ℂ) (v : ι → τ) :
    (∑ j : ι, (MvPolynomial.C (c j) : MvPolynomial τ ℂ) * MvPolynomial.X (v j)).totalDegree ≤ 1 := by
  refine (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun j _ => ?_)
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  rw [MvPolynomial.totalDegree_C, zero_add]
  exact (MvPolynomial.totalDegree_X _).le

theorem UpperTheory.Reformulated.B.TotalDegreeLinear.main :
    ∀ {ι A B : Type} [inst : Fintype ι] (g h : Matrix ι ι ℂ) (p : UpperTheory.Reformulated.B.TotalDegreeLinear.PV ι A B),
      MvPolynomial.totalDegree ((UpperTheory.Reformulated.B.TotalDegreeLinear.sub g h : UpperTheory.Reformulated.B.TotalDegreeLinear.PV ι A B → UpperTheory.Reformulated.B.TotalDegreeLinear.PV ι A B) p) ≤
        MvPolynomial.totalDegree p := by
  intro ι A B _ g h p
  refine UpperTheory.Reformulated.B.TotalDegreeLinear.totalDegree_aeval_le _ ?_ p
  rintro (x | y)
  · exact UpperTheory.Reformulated.B.TotalDegreeLinear.totalDegree_linear_le _ _
  · exact UpperTheory.Reformulated.B.TotalDegreeLinear.totalDegree_linear_le _ _
