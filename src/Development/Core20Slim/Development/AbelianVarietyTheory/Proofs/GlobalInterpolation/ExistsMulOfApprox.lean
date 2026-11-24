module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SubstitutionAdjoint
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SubDSharpInDeg
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.GaloisGeometry.TrueWtAddSSNonneg
public import Formalism.LocalRingCardinality.DataCoeff
public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Formalism.LocalToGlobal.KernelLattices.ThDistC
public import Init.Classical
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Function
public import Mathlib.Data.Set.Operations
public import Mathlib.Data.Sum.Basic
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.Order.CompleteLattice.Defs
public import Mathlib.Order.Disjoint
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic

@[expose] public section

open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint
open scoped Matrix

noncomputable section

namespace GlobalTheory.JetPoint

section Expand

variable {K L : Type} [Field K] [Field L] {ι : Type} [Fintype ι] {a b : ℕ}

abbrev expL (μ : ((ι × Fin b × Fin b) ⊕ DVar ι a b) →₀ ℕ) : (ι × Fin b × Fin b) →₀ ℕ :=
  μ.comapDomain Sum.inl Sum.inl_injective.injOn

abbrev expR (μ : ((ι × Fin b × Fin b) ⊕ DVar ι a b) →₀ ℕ) : DVar ι a b →₀ ℕ :=
  μ.comapDomain Sum.inr Sum.inr_injective.injOn

omit [Fintype ι] in
theorem constr_monomial {σ V : Type} [AddCommGroup V] [Module K V] (f : (σ →₀ ℕ) → V) (μ : σ →₀ ℕ) (c : K) :
    (basisMonomials σ K).constr K f (monomial μ c) = c • f μ := by
  have h : (monomial μ c : MvPolynomial σ K) = c • basisMonomials σ K μ := by
    rw [coe_basisMonomials, smul_monomial, smul_eq_mul, mul_one]
  rw [h, map_smul, Module.Basis.constr_basis]

omit [Fintype ι] in
theorem jetLin_eq_sum (J : (DVar ι a b →₀ ℕ) → K) (Q : MvPolynomial ((ι × Fin b × Fin b) ⊕ DVar ι a b) K) :
    jetLin J Q = ∑ μ ∈ Q.support, J (expR μ) • monomial (expL μ) (Q.coeff μ) := by
  conv_lhs => rw [Q.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [jetLin, constr_monomial, smul_monomial, smul_monomial, smul_eq_mul, smul_eq_mul, mul_comm]

theorem jetMap_eq_sum (J : (DVar ι a b →₀ ℕ) → K) (n : ι → ℕ) (P : Pol K ι a) :
    jetMap J n P = ∑ μ ∈ (subD K ι a b (sharp n P)).support,
      J (expR μ) • monomial (expL μ) ((subD K ι a b (sharp n P)).coeff μ) :=
  jetLin_eq_sum J _







theorem coe_jetOp (lam : ι → DomWeight a) (lam' : ι → DomWeight b) (J : (DVar ι a b →₀ ℕ) → K) (n : ι → ℕ)
    (F : VV K lam) (h : jetMap J n (F : Pol K ι a) ∈ VV K lam') :
    ((jetOp lam lam' J n F : VV K lam') : Pol K ι b) = jetMap J n (F : Pol K ι a) := by
  have h1 : retrVV K lam' ((⟨_, h⟩ : VV K lam') : Pol K ι b) = ⟨_, h⟩ := Submodule.projectionOnto_apply_left _ _
  exact congrArg Subtype.val h1




end Expand

section Integral

open Formalism.GradedWeylDivisibility (blockAct)

variable {K L Γ : Type} [Field K] [Field L] [LinearOrderedCommGroupWithZero Γ] {ι : Type} [Fintype ι] {a b : ℕ}










end Integral

section Closure

open Formalism.GradedWeylDivisibility (blockAct)

variable {K L Γ : Type} [Field K] [NumberField K] [Field L] [LinearOrderedCommGroupWithZero Γ]



end Closure

end GlobalTheory.JetPoint
