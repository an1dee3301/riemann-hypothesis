module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetVecEq
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.WeilOperatorRationalTranslateMemThetaFunctions
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHalfIdem
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemPrincipalCongruenceLevelSubgroupIffIntegralCo
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RationalPointsIntegralPointsMembership
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Classical
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Units
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Group.Submonoid.BigOperators
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Units
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Module.Submodule.Pointwise
public import Mathlib.Algebra.Order.Kleene
public import Mathlib.Algebra.Ring.Action.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Int.Units
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Algebra.Ring.Units
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Empty
public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Defs
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.Coprime.Basic
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Ideal.Pointwise
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

noncomputable section

namespace GlobalTheory.FunObj.StdDatum.DetCong

variable {D : D7}

theorem inc_mul_mem_hatId {I J : Ideal (𝓞 D.host.E)} {b : 𝓞 D.host.E} (hb : b ∈ I) {y : AE D}
    (hy : y ∈ hatId D J) : inc D (b : D.host.E) * y ∈ hatId D (I * J) := by
  induction hy using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨c, hc, s, hs, rfl⟩ := hx
    refine AddSubgroup.subset_closure ⟨b * c, Ideal.mul_mem_mul hb hc, s, hs, ?_⟩
    rw [← mul_assoc, ← map_mul]; rfl
  | zero => rw [mul_zero]; exact zero_mem _
  | add _ _ _ _ h1 h2 => rw [mul_add]; exact add_mem h1 h2
  | neg _ _ h => rw [mul_neg]; exact neg_mem h

theorem sgA_mem_hatId {𝔪 : Ideal (𝓞 D.host.E)} {y : AE D} (hy : y ∈ hatId D 𝔪) :
    sgA D y ∈ hatId D (D.host.conj • 𝔪) := by
  induction hy using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨c, hc, s, hs, rfl⟩ := hx
    refine AddSubgroup.subset_closure ⟨D.host.conj • c, Ideal.smul_mem_pointwise_smul _ _ _ hc, sgA D s,
      VacMove.sgA_mem D hs, ?_⟩
    rw [map_mul, GlobalTheory.NormSum.PtsMem.sgA_inc]; rfl
  | zero => rw [map_zero]; exact zero_mem _
  | add _ _ _ _ h1 h2 => rw [map_add]; exact add_mem h1 h2
  | neg _ _ h => rw [map_neg]; exact neg_mem h

theorem prod_sub_prod_mem {𝔪 : Ideal (𝓞 D.host.E)} {ι : Type*} (s : Finset ι) (f g : ι → AE D)
    (hf : ∀ i ∈ s, f i ∈ OhE D) (hg : ∀ i ∈ s, g i ∈ OhE D) (h : ∀ i ∈ s, f i - g i ∈ hatId D 𝔪) :
    (∏ i ∈ s, f i) - ∏ i ∈ s, g i ∈ hatId D 𝔪 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty, sub_self]; exact zero_mem _
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have e : f a * ∏ i ∈ s, f i - g a * ∏ i ∈ s, g i =
        f a * ((∏ i ∈ s, f i) - ∏ i ∈ s, g i) + (f a - g a) * ∏ i ∈ s, g i := by ring
    rw [e]
    refine add_mem (mul_mem_hatId (hf a (Finset.mem_insert_self a s))
      (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)) (fun i hi => hg i (Finset.mem_insert_of_mem hi))
        (fun i hi => h i (Finset.mem_insert_of_mem hi))))
      (mem_hatId_mul (prod_mem fun i hi => hg i (Finset.mem_insert_of_mem hi)) (h a (Finset.mem_insert_self a s)))

theorem det_sub_one_mem_hatId_of {𝔪 : Ideal (𝓞 D.host.E)} {a : ℕ} (M : Matrix (Fin a) (Fin a) (AE D))
    (hM : ∀ i j, M i j ∈ OhE D) (hC : ∀ i j, (M - 1) i j ∈ hatId D 𝔪) : M.det - 1 ∈ hatId D 𝔪 := by
  have h1 : ∀ i j, (1 : Matrix (Fin a) (Fin a) (AE D)) i j ∈ OhE D := fun i j => by
    rw [Matrix.one_apply]; split_ifs
    · exact one_mem _
    · exact zero_mem _
  rw [← Matrix.det_one (R := AE D) (n := Fin a), Matrix.det_apply, Matrix.det_apply, ← Finset.sum_sub_distrib]
  refine sum_mem fun σ _ => ?_
  rw [← smul_sub]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> rw [h]
  · rw [one_smul]
    exact prod_sub_prod_mem _ _ _ (fun i _ => hM _ _) (fun i _ => h1 _ _) (fun i _ => hC _ _)
  · rw [Units.neg_smul, one_smul]
    exact neg_mem (prod_sub_prod_mem _ _ _ (fun i _ => hM _ _) (fun i _ => h1 _ _) (fun i _ => hC _ _))

theorem det_sub_one_mem : ∀ (D : D7) {a : ℕ} (𝔪 : Ideal (𝓞 D.host.E)), IsCoprime 𝔪 (D.host.conj • 𝔪) →
    ∀ k : GA D a, k ∈ intG D a → CongOne D 𝔪 k →
      ((Matrix.GeneralLinearGroup.det (k : GL (Fin a) (AE D)) : (AE D)ˣ) : AE D) - 1 ∈
        hatId D (𝔪 * D.host.conj • 𝔪) := by
  intro D a 𝔪 hco k hk hc
  set u : AE D := ((Matrix.GeneralLinearGroup.det (k : GL (Fin a) (AE D)) : (AE D)ˣ) : AE D) with hu
  have hint := (mem_intG k).1 hk
  have huO : u ∈ OhE D := VacMove.det_int D _ hint
  have h1 : u - 1 ∈ hatId D 𝔪 := by
    rw [hu, Matrix.GeneralLinearGroup.val_det_apply]
    exact det_sub_one_mem_hatId_of _ (fun i j => (hint i j).1) hc
  have hn : u * sgA D u = 1 := VacMove.det_norm D k
  have h2 : u - 1 ∈ hatId D (D.host.conj • 𝔪) := by
    have e : u - 1 = -(u * sgA D (u - 1)) := by
      rw [map_sub, map_one, mul_sub, hn]; ring
    rw [e]
    exact neg_mem (mul_mem_hatId huO (sgA_mem_hatId h1))
  have hsup : 𝔪 ⊔ D.host.conj • 𝔪 = ⊤ := by
    rw [← Ideal.add_eq_sup, Ideal.isCoprime_iff_add.1 hco, Ideal.one_eq_top]
  have h1m : (1 : 𝓞 D.host.E) ∈ 𝔪 ⊔ D.host.conj • 𝔪 := by rw [hsup]; exact Submodule.mem_top
  obtain ⟨s, hs, t, ht, hst⟩ := Submodule.mem_sup.1 h1m
  have e : u - 1 = inc D (s : D.host.E) * (u - 1) + inc D (t : D.host.E) * (u - 1) := by
    rw [← add_mul, ← map_add (f := _), show (s : D.host.E) + t = ((s + t : 𝓞 D.host.E) : D.host.E) from rfl, hst]; simp
  rw [e]
  refine add_mem (inc_mul_mem_hatId hs h2) ?_
  rw [mul_comm 𝔪]
  exact inc_mul_mem_hatId ht h1

end GlobalTheory.FunObj.StdDatum.DetCong

end
