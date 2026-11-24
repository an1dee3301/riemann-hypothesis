module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SubstitutionAdjoint
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.GaloisGeometry.TrueWtAddSSNonneg
public import Formalism.GradedWeylDivisibility.StatementA
public import Formalism.GradedWeylDivisibility.StatementD
public import Formalism.LocalRingCardinality.DataCoeff
public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.PeriodLatticeFinitelyGenerated
public import Formalism.LocalToGlobal.KernelLattices.ThDistC
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Nat.Lemmas
public import Init.Data.Sum.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Units
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Ker
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Int.Units
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Units
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.SetNotation
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

@[expose] public section

open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint
open scoped Matrix

noncomputable section

namespace GlobalTheory.JetDeg

theorem algHom_hom {K σ ρ M N : Type} [CommRing K] [AddCommMonoid M] [AddCommMonoid N] (w : σ → M) (w' : ρ → N)
    (g : M →+ N) (φ : MvPolynomial σ K →ₐ[K] MvPolynomial ρ K)
    (hφ : ∀ v, IsWeightedHomogeneous w' (φ (X v)) (g (w v))) {f : MvPolynomial σ K} {d : M}
    (hf : IsWeightedHomogeneous w f d) : IsWeightedHomogeneous w' (φ f) (g d) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [f.as_sum, map_sum]
  refine IsWeightedHomogeneous.sum _ _ _ fun m hm => ?_
  have hd : Finsupp.weight w m = d := hf (mem_support_iff.mp hm)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [monomial_eq, map_mul, algHom_C, algebraMap_eq, Finsupp.prod, map_prod, ← hd, Finsupp.weight_apply,
    Finsupp.sum, map_sum]
  refine IsWeightedHomogeneous.C_mul ?_ _
  refine IsWeightedHomogeneous.prod _ _ _ fun v _ => ?_
  rw [map_pow, map_nsmul]
  exact (hφ v).pow _

variable {K : Type} [Field K] {ι : Type} [DecidableEq ι] {a b : ℕ}

def posW (a : ℕ) (τ : ι) : ι × Fin a × Fin a → ℕ := fun v => if v.1 = τ then 1 else 0

def derW (a b : ℕ) (τ : ι) : (ι × Fin b × Fin b) ⊕ DVar ι a b → ℕ :=
  Sum.elim (fun _ => 0) fun k => if k.1 = τ then 1 else 0

theorem blockEmb_hom (τ τ' : ι) (ν : Fin a → ℕ) {f : MvPolynomial (Fin a × Fin a) K}
    (hf : IsWeightedHomogeneous (Formalism.GradedWeylDivisibility.colW a a) f ν) :
    IsWeightedHomogeneous (posW a τ) (Formalism.GradedWeylDivisibility.blockEmb K τ' f) (if τ' = τ then ∑ i, ν i else 0) := by
  let g : (Fin a → ℕ) →+ ℕ :=
    { toFun := fun x => if τ' = τ then ∑ i, x i else 0
      map_zero' := by simp
      map_add' := by
        intro x y
        split_ifs <;> simp [Finset.sum_add_distrib] }
  refine algHom_hom (Formalism.GradedWeylDivisibility.colW a a) (posW a τ) g _ (fun v => ?_) hf
  have h := isWeightedHomogeneous_X K (posW a τ) (τ', v)
  have e : g (Formalism.GradedWeylDivisibility.colW a a v) = posW a τ (τ', v) := by
    simp [g, Formalism.GradedWeylDivisibility.colW, posW, Pi.single_apply]
  rw [e]
  simpa [Formalism.GradedWeylDivisibility.blockEmb] using h

theorem frDet_hom (τ τ' : ι) :
    IsWeightedHomogeneous (posW a τ) (frDet K a τ') (if τ' = τ then a else 0) := by
  rw [frDet, Matrix.det_apply]
  refine IsWeightedHomogeneous.sum _ _ _ fun σ _ => ?_
  have h : IsWeightedHomogeneous (posW a τ) (∏ i : Fin a, (X (τ', σ i, i) : Pol K ι a))
      (∑ _i : Fin a, if τ' = τ then 1 else 0) :=
    IsWeightedHomogeneous.prod _ _ _ fun i _ => isWeightedHomogeneous_X K (posW a τ) (τ', σ i, i)
  have e : (∑ _i : Fin a, if τ' = τ then 1 else 0) = if τ' = τ then a else 0 := by
    split_ifs <;> simp
  rw [e] at h
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h1 | h1
  · simpa [h1] using h
  · simpa [h1] using h.neg

theorem subD_hom (τ : ι) {P : Pol K ι a} {d : ℕ} (hP : IsWeightedHomogeneous (posW a τ) P d) :
    IsWeightedHomogeneous (derW a b τ) (subD K ι a b P) d := by
  refine algHom_hom (posW a τ) (derW a b τ) (AddMonoidHom.id ℕ) _ (fun v => ?_) hP
  rw [subD, aeval_X]
  split_ifs with h
  · refine IsWeightedHomogeneous.sum _ _ _ fun β _ => ?_
    have := (isWeightedHomogeneous_X K (derW a b τ) (Sum.inl (v.1, β, (⟨v.2.2.1, h⟩ : Fin b)))).mul
      (isWeightedHomogeneous_X K (derW a b τ) (Sum.inr (v.1, β, v.2.1)))
    simpa [derW, posW] using this
  · exact isWeightedHomogeneous_zero _ _ _

variable [Fintype ι]

theorem VV_hom (lam : ι → DomWeight a) (τ : ι) {P : Pol K ι a} (hP : P ∈ Formalism.L2.DIV.VV K lam) :
    IsWeightedHomogeneous (posW a τ) P (∑ i, (lam τ).natW i) := by
  have : Formalism.L2.DIV.VV K lam ≤ weightedHomogeneousSubmodule K (posW a τ) (∑ i, (lam τ).natW i) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨F, hF, rfl⟩
    have h := IsWeightedHomogeneous.prod Finset.univ (fun τ' => Formalism.GradedWeylDivisibility.blockEmb K τ' (F τ'))
      (fun τ' => if τ' = τ then ∑ i, (lam τ').natW i else 0) (w := posW a τ)
      fun τ' _ => blockEmb_hom τ τ' _ (hF τ').1
    simpa using h
  exact this hP

theorem sharp_hom (n : ι → ℕ) (τ : ι) {P : Pol K ι a} {d : ℕ} (hP : IsWeightedHomogeneous (posW a τ) P d) :
    IsWeightedHomogeneous (posW a τ) (sharp n P) (d + n τ * a) := by
  refine hP.mul ?_
  have h := IsWeightedHomogeneous.prod Finset.univ (fun τ' => frDet K a τ' ^ n τ')
    (fun τ' => n τ' • if τ' = τ then a else 0) (w := posW a τ)
    fun τ' _ => (frDet_hom τ τ').pow _
  simpa using h



end GlobalTheory.JetDeg



end
