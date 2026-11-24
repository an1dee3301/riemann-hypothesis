module

public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GaussianPlaneIntegrals.AssemblyAlt
public import Mathlib
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.NullSec
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Fin.Lemmas
public import Init.Data.Function
public import Init.Data.Int.Basic
public import Init.Data.Int.Lemmas
public import Init.Data.Int.Order
public import Init.Data.List.Basic
public import Init.Data.List.Lemmas
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.GroupWithZero.Action
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Submonoid.Basic
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Submonoid.Membership
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.BigOperators
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Module.Submodule.Basic
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.IsEmpty.Defs
public import Mathlib.Basic.Logic.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Range
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Basis
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.LinearAlgebra.Vandermonde
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Hom.Basic
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Tactic.Ring.RingNF

@[expose] public section

noncomputable section

open MvPolynomial

namespace PositivityTheory.Rg.Sw.FFTSteps

namespace PowSpanB

variable {m n : ℕ} (ε : Fin m → Bool)

def lf (b : Matrix (Fin n) (Fin n) ℂ) : PX m n := ∑ i, ∑ j, b i j • (Qp ε j i : PX m n)

theorem lf_eq (b : Matrix (Fin n) (Fin n) ℂ) :
    (∑ i, ∑ j, C (b i j) * (Qp ε j i : PX m n)) = lf ε b := by
  simp only [lf, C_mul']

theorem lf_add (b c : Matrix (Fin n) (Fin n) ℂ) : lf ε (b + c) = lf ε b + lf ε c := by
  simp only [lf, Matrix.add_apply, add_smul, Finset.sum_add_distrib]

theorem lf_smul (z : ℂ) (b : Matrix (Fin n) (Fin n) ℂ) : lf ε (z • b) = z • lf ε b := by
  simp only [lf, Matrix.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]

theorem lf_single (a b : Fin n) : lf ε (Matrix.single b a (1 : ℂ)) = (Qp ε a b : PX m n) := by
  simp [lf, Matrix.single_apply, ite_smul, ite_and]

def W : Set (PX m n) := {w | ∃ h : Matrix (Fin n) (Fin n) ℂ, h.IsHermitian ∧ w = lf ε h}

def S : Submodule ℂ (PX m n) :=
  Submodule.span ℂ {R | ∃ (b : Matrix (Fin n) (Fin n) ℂ) (k : ℕ), b.IsHermitian ∧
    R = (∑ i, ∑ j, C (b i j) * (Qp ε j i : PX m n)) ^ k}

theorem pow_mem {w : PX m n} (hw : w ∈ W ε) (k : ℕ) : w ^ k ∈ S ε := by
  obtain ⟨h, hh, rfl⟩ := hw
  exact Submodule.subset_span ⟨h, k, hh, by rw [lf_eq]⟩

theorem zero_mem_W : (0 : PX m n) ∈ W ε :=
  ⟨0, Matrix.isHermitian_zero, by simp [lf]⟩

theorem natCast_smul_add_mem_W {w v : PX m n} (hw : w ∈ W ε) (hv : v ∈ W ε) (t : ℕ) : (t : ℂ) • v + w ∈ W ε := by
  obtain ⟨h1, hh1, rfl⟩ := hw
  obtain ⟨h2, hh2, rfl⟩ := hv
  refine ⟨(t : ℂ) • h2 + h1, ?_, by rw [lf_add, lf_smul]⟩
  show Matrix.conjTranspose ((t : ℂ) • h2 + h1) = _
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, hh2.eq, hh1.eq]
  simp

theorem herm_decomp (b : Matrix (Fin n) (Fin n) ℂ) : ∃ H1 H2 : Matrix (Fin n) (Fin n) ℂ,
    H1.IsHermitian ∧ H2.IsHermitian ∧ b = H1 + Complex.I • H2 := by
  refine ⟨(1 / 2 : ℂ) • (b + Matrix.conjTranspose b), (-Complex.I / 2) • (b - Matrix.conjTranspose b), ?_, ?_, ?_⟩
  · show Matrix.conjTranspose ((1 / 2 : ℂ) • (b + Matrix.conjTranspose b)) = _
    ext i j
    simp [Matrix.conjTranspose_apply, Matrix.add_apply, Matrix.smul_apply]
    ring
  · show Matrix.conjTranspose ((-Complex.I / 2) • (b - Matrix.conjTranspose b)) = _
    ext i j
    simp [Matrix.conjTranspose_apply, Matrix.sub_apply, Matrix.smul_apply]
    ring
  · ext i j
    simp [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply]
    ring_nf
    rw [Complex.I_sq]
    ring

private theorem coeff_mem_of_forall_natCast_poly_sum_mem {M : Type*} [AddCommGroup M] [Module ℂ M] (T : Submodule ℂ M) (N : ℕ)
    (c : ℕ → M) (h : ∀ t : ℕ, ∑ j ∈ Finset.range (N + 1), ((t : ℂ) ^ j) • c j ∈ T)
    (k : ℕ) (hk : k < N + 1) : c k ∈ T := by
  let V : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ := Matrix.vandermonde (fun t : Fin (N + 1) => ((t : ℕ) : ℂ))
  have hV : IsUnit V.det := by
    refine isUnit_iff_ne_zero.mpr (Matrix.det_vandermonde_ne_zero_iff.mpr ?_)
    intro a b hab
    exact Fin.ext (Nat.cast_injective hab)
  have key : ∑ t : Fin (N + 1), (V⁻¹ ⟨k, hk⟩ t) • (∑ j ∈ Finset.range (N + 1), (((t : ℕ) : ℂ) ^ j) • c j) = c k := by
    have e : ∀ t : Fin (N + 1), (∑ j ∈ Finset.range (N + 1), (((t : ℕ) : ℂ) ^ j) • c j)
        = ∑ j : Fin (N + 1), V t j • c j := by
      intro t
      rw [← Fin.sum_univ_eq_sum_range (fun j => (((t : ℕ) : ℂ) ^ j) • c j)]
      simp [V, Matrix.vandermonde_apply]
    simp_rw [e, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_smul]
    have hm : ∀ j : Fin (N + 1), ∑ t : Fin (N + 1), V⁻¹ ⟨k, hk⟩ t * V t j = (V⁻¹ * V) ⟨k, hk⟩ j := by
      intro j
      rw [Matrix.mul_apply]
    simp_rw [hm, Matrix.nonsing_inv_mul _ hV, Matrix.one_apply, ite_smul, one_smul, zero_smul]
    simp
  rw [← key]
  exact Submodule.sum_mem _ (fun t _ => T.smul_mem _ (h t))

theorem core : ∀ l : List (PX m n), (∀ v ∈ l, v ∈ W ε) → ∀ w ∈ W ε, ∀ r : ℕ, l.prod * w ^ r ∈ S ε := by
  intro l
  induction l with
  | nil =>
    intro _ w hw r
    simpa using pow_mem ε hw r
  | cons v l ih =>
    intro hl w hw r
    have hv : v ∈ W ε := hl v (by simp)
    have ih' := ih (fun u hu => hl u (by simp [hu]))
    have h1 : ∀ t : ℕ, ∑ j ∈ Finset.range (r + 1 + 1), ((t : ℂ) ^ j) •
        (l.prod * (v ^ j * w ^ (r + 1 - j) * (((r + 1).choose j : ℕ) : PX m n))) ∈ S ε := by
      intro t
      have := ih' _ (natCast_smul_add_mem_W ε hw hv t) (r + 1)
      convert this using 1
      rw [add_pow, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [smul_pow, smul_mul_assoc, smul_mul_assoc, mul_smul_comm]
    have h2 := coeff_mem_of_forall_natCast_poly_sum_mem (S ε) (r + 1) _ h1 1 (by omega)
    have e : (v :: l).prod * w ^ r = ((r + 1 : ℕ) : ℂ)⁻¹ •
        (l.prod * (v ^ 1 * w ^ (r + 1 - 1) * (((r + 1).choose 1 : ℕ) : PX m n))) := by
      rw [Nat.choose_one_right, pow_one, Nat.add_sub_cancel, List.prod_cons]
      rw [show (((r + 1 : ℕ)) : PX m n) = ((r + 1 : ℕ) : ℂ) • (1 : PX m n) by
        rw [Nat.cast_smul_eq_nsmul, nsmul_one]]
      rw [mul_smul_comm, mul_smul_comm, smul_smul,
        inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero r)), one_smul]
      ring
    rw [e]
    exact (S ε).smul_mem _ h2

private theorem list_prod_mul_span_prod_mem_S : ∀ l : List (PX m n), (∀ x ∈ l, x ∈ Submodule.span ℂ (W ε)) →
    ∀ q : List (PX m n), (∀ v ∈ q, v ∈ W ε) → q.prod * l.prod ∈ S ε := by
  intro l
  induction l with
  | nil =>
    intro _ q hq
    simpa using core ε q hq 0 (zero_mem_W ε) 0
  | cons x l ih =>
    intro hl q hq
    have hx : x ∈ Submodule.span ℂ (W ε) := hl x (by simp)
    have hl' : ∀ y ∈ l, y ∈ Submodule.span ℂ (W ε) := fun y hy => hl y (by simp [hy])
    clear hl
    rw [List.prod_cons]
    induction hx using Submodule.span_induction with
    | mem y hy =>
      have := ih hl' (y :: q) (by
        intro v hv
        rcases List.mem_cons.mp hv with h | h
        · exact h ▸ hy
        · exact hq v h)
      rw [List.prod_cons] at this
      rw [← mul_assoc, mul_comm q.prod y]
      exact this
    | zero => simp
    | add a b _ _ ha hb =>
      rw [add_mul, mul_add]
      exact add_mem ha hb
    | smul z a _ ha =>
      rw [smul_mul_assoc, mul_smul_comm]
      exact (S ε).smul_mem z ha

theorem span_eq :
    (Algebra.adjoin ℂ (Set.range fun ij : Fin n × Fin n => (Qp ε ij.1 ij.2 : PX m n))).toSubmodule = S ε := by
  apply le_antisymm
  · rw [Algebra.adjoin_eq_span]
    refine Submodule.span_le.mpr ?_
    intro x hx
    obtain ⟨l, hl, rfl⟩ := Submonoid.exists_list_of_mem_closure hx
    have := list_prod_mul_span_prod_mem_S ε l (by
      intro y hy
      obtain ⟨⟨a, b⟩, rfl⟩ := hl y hy
      obtain ⟨H1, H2, h1, h2, hb⟩ := herm_decomp (Matrix.single b a (1 : ℂ))
      have e : (Qp ε a b : PX m n) = lf ε H1 + Complex.I • lf ε H2 := by
        rw [← lf_single, hb, lf_add, lf_smul]
      show (Qp ε a b : PX m n) ∈ _
      rw [e]
      exact add_mem (Submodule.subset_span ⟨H1, h1, rfl⟩)
        (Submodule.smul_mem _ _ (Submodule.subset_span ⟨H2, h2, rfl⟩))) [] (by simp)
    simpa using this
  · refine Submodule.span_le.mpr ?_
    rintro R ⟨b, k, _, rfl⟩
    show _ ∈ Algebra.adjoin ℂ _
    refine Subalgebra.pow_mem _ (Subalgebra.sum_mem _ (fun i _ => Subalgebra.sum_mem _ (fun j _ => ?_))) k
    refine Subalgebra.mul_mem _ ?_ (Algebra.subset_adjoin ⟨(j, i), rfl⟩)
    rw [← MvPolynomial.algebraMap_eq]
    exact Subalgebra.algebraMap_mem _ _

end PowSpanB

theorem powSpan : PowSpan := fun _ _ ε => PowSpanB.span_eq ε

end PositivityTheory.Rg.Sw.FFTSteps
