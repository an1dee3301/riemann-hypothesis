module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.InterlacingEquivariance
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SplitLastBlockActX
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TensorMapDescent
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.ColLexInitMinor
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.HighestWeightVectorNeZero
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LHwlineLemmas
public import Formalism.GradedWeylDivisibility.StatementA
public import Formalism.LocalRingCardinality.DataCoeff
public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.InterlaceDifferenceShiftInvariant
public import Init.Classical
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Fin.Basic
public import Init.Data.Fin.Lemmas
public import Init.Data.Int.Basic
public import Init.Data.Int.Lemmas
public import Init.Data.Int.Order
public import Init.Data.Nat.Basic
public import Init.Data.NeZero
public import Init.Data.Zero
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Omega.Logic
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Even
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Order.Antidiag.Prod
public import Mathlib.Algebra.Order.SuccPred
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.IsEmpty.Defs
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fin.SuccPred
public import Mathlib.Data.Finset.BooleanAlgebra
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Empty
public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Finset.Union
public import Mathlib.Data.Finsupp.Antidiagonal
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Finsupp.SMulWithZero
public import Mathlib.Data.Finsupp.Single
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Fin.Basic
public import Mathlib.Order.Lattice
public import Mathlib.Order.Nat
public import Mathlib.Order.SuccPred.Nat
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic

@[expose] public section

open MvPolynomial NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col GlobalTheory.IndefiniteRowSideFullHecke.InterlacingEquivariance GlobalTheory.BranchFormula

noncomputable section

namespace GlobalTheory.XiTopCoef

section Top

variable {σ A : Type} [CommRing A] (w : σ → ℕ)

def TopTerm (f : MvPolynomial σ A) (d : σ →₀ ℕ) (c : A) : Prop :=
  AddMonoidAlgebra.coeff f d = c ∧ ∀ m ∈ f.support, m = d ∨ Finsupp.weight w m < Finsupp.weight w d

variable {w}

theorem TopTerm.C (c : A) : TopTerm w (C c : MvPolynomial σ A) 0 c := by
  classical
  refine ⟨by simp, fun m hm => Or.inl ?_⟩
  by_contra h
  rw [mem_support_iff, coeff_C, if_neg (Ne.symm h)] at hm
  exact hm rfl

theorem TopTerm.mul {f g : MvPolynomial σ A} {d e : σ →₀ ℕ} {c c' : A} (hf : TopTerm w f d c) (hg : TopTerm w g e c') :
    TopTerm w (f * g) (d + e) (c * c') := by
  classical
  constructor
  · rw [coeff_mul, Finset.sum_eq_single (d, e), hf.1, hg.1]
    · rintro ⟨x, y⟩ hxy hne
      by_contra h0
      have hx := hf.2 x (mem_support_iff.2 (left_ne_zero_of_mul h0))
      have hy := hg.2 y (mem_support_iff.2 (right_ne_zero_of_mul h0))
      have hs : x + y = d + e := by simpa using hxy
      have hw := congrArg (Finsupp.weight w) hs
      rw [map_add (f := _), map_add (f := _)] at hw
      rcases hx with rfl | hx <;> rcases hy with rfl | hy
      · exact hne rfl
      all_goals omega
    · intro h
      exact absurd (by simp) h
  · intro m hm
    obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_add.1 (support_mul f g hm)
    rw [map_add (f := _), map_add (f := _)]
    rcases hf.2 x hx with rfl | hx <;> rcases hg.2 y hy with rfl | hy
    · exact Or.inl rfl
    all_goals right; omega

theorem TopTerm.pow {f : MvPolynomial σ A} {d : σ →₀ ℕ} {c : A} (hf : TopTerm w f d c) (k : ℕ) :
    TopTerm w (f ^ k) (k • d) (c ^ k) := by
  induction k with
  | zero => simpa using TopTerm.C (w := w) (1 : A)
  | succ k ih => rw [pow_succ, pow_succ, succ_nsmul]; exact ih.mul hf

theorem TopTerm.prod {ι : Type} (s : Finset ι) {f : ι → MvPolynomial σ A} {d : ι → σ →₀ ℕ} {c : ι → A}
    (h : ∀ i, TopTerm w (f i) (d i) (c i)) : TopTerm w (∏ i ∈ s, f i) (∑ i ∈ s, d i) (∏ i ∈ s, c i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using TopTerm.C (w := w) (1 : A)
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, Finset.prod_insert ha]; exact (h a).mul ih

theorem TopTerm.linear {k : ℕ} (v : Fin (k + 1) → σ) (c : Fin (k + 1) → A)
    (hv : ∀ q : Fin k, w (v q.castSucc) < w (v (Fin.last k))) :
    TopTerm w (∑ q, X (v q) * MvPolynomial.C (c q)) (Finsupp.single (v (Fin.last k)) 1) (c (Fin.last k)) := by
  classical
  have e : ∀ q, (X (v q) * MvPolynomial.C (c q) : MvPolynomial σ A) = monomial (Finsupp.single (v q) 1) (c q) := by
    intro q
    rw [mul_comm, C_mul_X_eq_monomial]
  simp only [e]
  constructor
  · rw [coeff_sum, Fin.sum_univ_castSucc, Finset.sum_eq_zero, zero_add, coeff_monomial, if_pos rfl]
    intro q _
    rw [coeff_monomial, if_neg]
    intro h
    have h1 := Finsupp.single_left_injective one_ne_zero h
    have := hv q
    rw [h1] at this
    exact lt_irrefl _ this
  · intro m hm
    obtain ⟨q, -, hq⟩ := Finset.mem_biUnion.1 (support_sum hm)
    have hq' := Finset.mem_singleton.1 (support_monomial_subset hq)
    subst hq'
    induction q using Fin.lastCases with
    | last => exact Or.inl rfl
    | cast q => right; simpa [Finsupp.weight_single] using hv q

end Top

variable (K : Type) [Field K] {N n : ℕ} (hN : N = n + 1)

def lp (n k : ℕ) : Pol K Unit n :=
  if h : k ≤ n then rename (fun v : Fin n × Fin n => (((), v) : Unit × Fin n × Fin n)) (Formalism.GradedWeylDivisibility.lpMinor K k h h) else 1

theorem lp_eq {k : ℕ} (h : k ≤ n) :
    lp K n k = (Matrix.of fun p q : Fin k => (X ((), Fin.castLE h p, Fin.castLE h q) : Pol K Unit n)).det := by
  rw [lp, dif_pos h, Formalism.GradedWeylDivisibility.lpMinor, AlgHom.map_det]
  congr 1
  ext p q
  simp

theorem lp_zero : lp K n 0 = 1 := by
  rw [lp_eq K (Nat.zero_le n), Matrix.det_isEmpty]

theorem split_lp {k : ℕ} (h : k ≤ n) (h' h'' : k ≤ N) :
    splitLast K Unit hN (rename (fun v : Fin N × Fin N => (((), v) : Unit × Fin N × Fin N)) (Formalism.GradedWeylDivisibility.lpMinor K k h' h'')) =
      C (lp K n k) := by
  rw [lp_eq K h, Formalism.GradedWeylDivisibility.lpMinor, AlgHom.map_det, AlgHom.map_det, RingHom.map_det]
  congr 1
  ext1 p q
  simp only [AlgHom.mapMatrix_apply, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, rename_X]
  exact splitLast_X_up K Unit hN () (Fin.castLE h p) (Fin.castLE h q)

theorem weightedLeadingTerm_split_zMinor (i : Fin n) :
    TopTerm (fun p : Unit × Fin n => p.2.val)
      (splitLast K Unit hN (rename (fun v : Fin N × Fin N => (((), v) : Unit × Fin N × Fin N)) (Br.zMinor K hN i)))
      (Finsupp.single ((), i) 1) (lp K n i) := by
  have hi : i.val + 1 ≤ n := i.2
  have hi' : i.val ≤ n := i.2.le
  have key := TopTerm.linear (w := fun p : Unit × Fin n => p.2.val) (k := i.val) (fun q => ((), Fin.castLE hi q))
    (fun q => (-1) ^ (i.val + q.val) * (Matrix.of fun p r : Fin i.val =>
      (X ((), Fin.castLE hi' p, Fin.castLE hi (q.succAbove r)) : Pol K Unit n)).det) (fun q => by simp)
  convert key using 1
  · rw [Br.zMinor, Formalism.GradedWeylDivisibility.initMinor, AlgHom.map_det, AlgHom.map_det, Matrix.det_succ_row _ (Fin.last i.val)]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [map_mul, RingHom.map_det, map_pow, map_neg, map_one, mul_left_comm, ← mul_assoc]
    congr 2
    · simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, rename_X, Fin.val_last, lt_irrefl, dif_neg,
        not_false_eq_true]
      exact splitLast_X_lastRow K Unit hN () (Fin.castLE hi q)
    · ext1 p r
      simp only [AlgHom.mapMatrix_apply, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, rename_X,
        Matrix.submatrix_apply, Fin.succAbove_last, Fin.val_castSucc, p.2, dif_pos]
      exact splitLast_X_up K Unit hN () (Fin.castLE hi' p) (Fin.castLE hi (q.succAbove r))
  · rfl
  · rw [lp_eq K hi', Fin.val_last, ← two_mul, pow_mul]
    simp only [Fin.succAbove_last, even_two, Even.neg_pow, one_pow, one_mul]
    rfl

theorem prod_shift {M : Type} [CommMonoid M] (P : ℕ → M) (h0 : P 0 = 1) (b : Fin n → ℕ) :
    ∏ i : Fin n, P i ^ b i = ∏ i : Fin n, P (i + 1) ^ Formalism.GradedWeylDivisibility.nuNext b i := by
  cases n with
  | zero => simp
  | succ m =>
    rw [Fin.prod_univ_succ, Fin.prod_univ_castSucc]
    simp [h0, Formalism.GradedWeylDivisibility.nuNext]
    rfl

theorem exp_eq (lam : DomWeight N) (sg : DomWeight n) (hI : Br.Interlace hN lam sg) (hS : Br.SameShift lam sg) (i : Fin n) :
    (Br.aBr hN lam sg i).toNat + Formalism.GradedWeylDivisibility.nuNext (fun s => (Br.bBr hN lam sg s).toNat) i =
      sg.natW i - Formalism.GradedWeylDivisibility.nuNext sg.natW i := by
  subst hN
  have hn : 0 < n := i.pos
  have h1 := (hI i).1
  have e1 : sg.detShift = sg.w ⟨n - 1, by omega⟩ := dif_pos hn
  have e2 : lam.detShift = lam.w ⟨n, by omega⟩ := dif_pos (Nat.succ_pos n)
  unfold Br.SameShift at hS
  unfold Formalism.GradedWeylDivisibility.nuNext
  split_ifs with h
  · have h2 := (hI ⟨i.val + 1, h⟩).2
    have h3 : sg.w ⟨n - 1, by omega⟩ ≤ sg.w ⟨i.val + 1, h⟩ := sg.anti (by simp only [Fin.le_def]; omega)
    simp only [Br.aBr, Br.bBr, Br.iS, Br.iC, DomWeight.natW] at *
    omega
  · have hi : i = ⟨n - 1, by omega⟩ := Fin.ext (by have := i.2; simp only; omega)
    have e3 : lam.w (Br.iS rfl i) = lam.w ⟨n, by omega⟩ := by
      congr 1
      exact Fin.ext (by have := i.2; simp only [Br.iS]; omega)
    rw [← hi] at e1
    simp only [Br.aBr, DomWeight.natW] at *
    omega

theorem coefLast_xi : ∀ (K : Type) [Field K] (N n : ℕ) (hN : N = n + 1) (lam : DomWeight N) (sg : DomWeight n), Br.Interlace hN lam sg → Br.SameShift lam sg → Br.coefLast (K := K) hN (Br.bExp hN (fun _ : Unit => lam) (fun _ : Unit => sg)) (rename (fun v : Fin N × Fin N => (((), v) : Unit × Fin N × Fin N)) (Br.xiBr K hN lam sg)) = rename (fun v : Fin n × Fin n => (((), v) : Unit × Fin n × Fin n)) (extremal K n sg) := by
  intro K _ N n hN lam sg hI hS
  have key := (TopTerm.prod (w := fun p : Unit × Fin n => p.2.val) Finset.univ fun i : Fin n =>
    ((TopTerm.C (lp K n (i.val + 1))).pow (Br.aBr hN lam sg i).toNat).mul
      ((weightedLeadingTerm_split_zMinor K hN i).pow (Br.bBr hN lam sg i).toNat)).1
  rw [coefLast_eq_coeff, Br.xiBr, map_prod, map_prod]
  simp only [map_mul, map_pow]
  have hsp : ∀ i : Fin n, _ := fun i : Fin n =>
    split_lp K hN (k := i.val + 1) i.2 (by have := i.2; omega) (by have := i.2; omega)
  simp only [hsp]
  refine Eq.trans (congrArg (fun e => AddMonoidAlgebra.coeff _ e) ?_) (key.trans ?_)
  · ext ⟨u, s⟩
    simp [Br.bExp, Finsupp.finsetSum_apply, Finsupp.single_apply]
  · rw [Finset.prod_mul_distrib, prod_shift (lp K n) (lp_zero K) fun s => (Br.bBr hN lam sg s).toNat,
      ← Finset.prod_mul_distrib, extremal, Formalism.GradedWeylDivisibility.hw, map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← pow_add, exp_eq hN lam sg hI hS, map_pow, lp, dif_pos (show i.val + 1 ≤ n from i.2)]

end GlobalTheory.XiTopCoef
