module

public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GaussianPlaneIntegrals.CycFFTA
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GaussianPlaneIntegrals.AssemblyAlt
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GaussianPlaneIntegrals.AssemblyT
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.NullSec
public import Init.ByCases
public import Init.Core
public import Init.Data.Bool
public import Init.Data.Sum.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.MvPolynomial.Monad
public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Filter
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Sets
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Data.Subtype
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Matrix.Defs

@[expose] public section

noncomputable section

open MvPolynomial

namespace PositivityTheory.Rg.Sw.FFTSteps.CycF

variable {m n : ℕ} {ε : Fin m → Bool}

theorem sum_blk (β : Bool) (v : Matrix (Rw ε β) (Rw ε β) ℂ) (a : Rw ε β) (i : Fin n) (t : Bool) :
    ∑ b, C (blk ε β v a.1 b) * (X (b, i, t) : PX m n) = ∑ j : Rw ε β, C (v a j) * X (j.1, i, t) := by
  rw [← sum_rw β (fun j => C (v a j) * (X (j.1, i, t) : PX m n))]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [blk_of β v a.2]
  split_ifs <;> simp

theorem sum_blk_star (β : Bool) (v : Matrix (Rw ε β) (Rw ε β) ℂ) (a : Rw ε β) (i : Fin n) (t : Bool) :
    ∑ b, C (star (blk ε β v a.1 b)) * (X (b, i, t) : PX m n) = ∑ j : Rw ε β, C (star (v a j)) * X (j.1, i, t) := by
  rw [← sum_rw β (fun j => C (star (v a j)) * (X (j.1, i, t) : PX m n))]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [blk_of β v a.2]
  split_ifs <;> simp

theorem sum_blk_other (β : Bool) (v : Matrix (Rw ε β) (Rw ε β) ℂ) {a : Fin m} (ha : ¬ ε a = β) (i : Fin n)
    (t : Bool) (st : Bool) :
    ∑ b, C (if st then star (blk ε β v a b) else blk ε β v a b) * (X (b, i, t) : PX m n) = X (a, i, t) := by
  simp only [blk_of_not β v ha]
  cases st <;> simp [apply_ite star, ite_mul]

theorem act_emb_same (β : Bool) (v : Matrix (Rw ε β) (Rw ε β) ℂ) :
    (act (n := n) (blk ε β v)).comp (emb ε β) = (emb ε β).comp (sub v (v.map star)) := by
  refine MvPolynomial.algHom_ext fun x => ?_
  rcases x with ⟨i, a⟩ | ⟨i, a⟩
  set_option synthInstance.maxHeartbeats 100000 in
    · simp [act, emb, sub, jv, sum_blk, map_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    · simpa [act, emb, sub, jv, map_sum] using sum_blk_star (n := n) β v i a true

theorem act_emb_other (β β' : Bool) (hne : β' ≠ β) (v : Matrix (Rw ε β) (Rw ε β) ℂ) :
    (act (n := n) (blk ε β v)).comp (emb ε β') = emb ε β' := by
  refine MvPolynomial.algHom_ext fun x => ?_
  rcases x with ⟨i, a⟩ | ⟨i, a⟩
  · have hi : ¬ ε i.1 = β := fun h => hne (i.2.symm.trans h)
    have := sum_blk_other (n := n) β v hi a false false
    simp only [Bool.false_eq_true, if_false] at this
    simp [act, emb, jv, this]
  · have hi : ¬ ε i.1 = β := fun h => hne (i.2.symm.trans h)
    have := sum_blk_other (n := n) β v hi a true true
    simp only [if_true] at this
    simpa [act, emb, jv] using this

theorem emb_pair (β : Bool) (a b : Fin n) :
    emb ε β (∑ i : Rw ε β, (X (Sum.inl (i, a)) : PV (Rw ε β) (Fin n) (Fin n)) * X (Sum.inr (i, b))) = Qb ε β b a := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, emb, rename_X, jv, Sum.elim_inl, Sum.elim_inr, Qb]
  rw [Finset.sum_subtype (Finset.univ.filter (fun x : Fin m => ε x = β)) (p := fun x => ε x = β) (by simp)]
  exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

theorem emb_pairAlg (β : Bool) {p : PV (Rw ε β) (Fin n) (Fin n)} (hp : p ∈ pairAlg (Rw ε β) (Fin n) (Fin n)) :
    emb ε β p ∈ Algebra.adjoin ℂ (Set.range fun k : Bool × Fin n × Fin n => (Qb ε k.1 k.2.1 k.2.2 : PX m n)) := by
  have h1 : emb ε β p ∈ (pairAlg (Rw ε β) (Fin n) (Fin n)).map (emb ε β) := Subalgebra.mem_map.2 ⟨p, hp, rfl⟩
  rw [pairAlg, AlgHom.map_adjoin] at h1
  refine Algebra.adjoin_mono ?_ h1
  rintro _ ⟨_, ⟨⟨a, b⟩, rfl⟩, rfl⟩
  exact ⟨(β, b, a), (emb_pair β a b).symm⟩

end PositivityTheory.Rg.Sw.FFTSteps.CycF
