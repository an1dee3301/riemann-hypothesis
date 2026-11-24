module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SigV
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Classical
public import Init.Core
public import Init.Data.Function
public import Init.Data.Int.Basic
public import Init.Data.NeZero
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Prod
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Ker
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Module.Torsion.Free
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.NoZeroSMulDivisors.Basic
public import Mathlib.Algebra.NoZeroSMulDivisors.Defs
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Nontrivial.Defs
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.LinearAlgebra.TensorProduct.Associator
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.Abel

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl IsDedekindDomain NumberField GlobalTheory.FixedUnitNorm
open scoped TensorProduct

namespace GlobalTheory.CoordUnique

theorem coords_unique_of_field {K E A : Type*} [Field K] [Ring E] [Nontrivial E] [Algebra K E] [AddCommGroup A]
    [Module K A] (w : E) (hw : ∀ f : K, algebraMap K E f ≠ w) (a b : A)
    (h : a ⊗ₜ[K] (1 : E) + b ⊗ₜ[K] w = 0) : a = 0 ∧ b = 0 := by
  obtain ⟨φ, hφ⟩ : ∃ φ : (K × K) →ₗ[K] E, ∀ p, φ p = p.1 • (1 : E) + p.2 • w :=
    ⟨{ toFun := fun p => p.1 • (1 : E) + p.2 • w,
       map_add' := fun p q => by simp only [Prod.fst_add, Prod.snd_add, add_smul]; abel,
       map_smul' := fun c p => by
        simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, mul_smul, smul_add, RingHom.id_apply] },
      fun p => rfl⟩
  have hinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨s, t⟩ hst
    rw [hφ] at hst
    by_cases ht : t = 0
    · subst ht
      simp only [zero_smul, add_zero, smul_eq_zero, one_ne_zero, or_false] at hst
      simp [hst]
    · exfalso
      apply hw (-s / t)
      have h1 : t • w = -(s • (1 : E)) := eq_neg_of_add_eq_zero_right hst
      have h2 : w = t⁻¹ • (-(s • (1 : E))) := by
        rw [← h1, smul_smul, inv_mul_cancel₀ ht, one_smul]
      rw [h2, Algebra.algebraMap_eq_smul_one, smul_neg, smul_smul, div_eq_mul_inv, neg_mul, neg_smul, mul_comm]
  have hinj' := Module.Flat.lTensor_preserves_injective_linearMap (M := A) φ hinj
  have hx : φ.lTensor A (a ⊗ₜ[K] ((1 : K), (0 : K)) +
      b ⊗ₜ[K] ((0 : K), (1 : K))) = 0 := by
    rw [map_add (f := _), LinearMap.lTensor_tmul, LinearMap.lTensor_tmul, hφ, hφ]
    simpa using h
  rw [← map_zero (φ.lTensor A)] at hx
  have hx0 := hinj' hx
  have ha : TensorProduct.rid K A
      ((LinearMap.fst K K K).lTensor A
        (a ⊗ₜ[K] ((1 : K), (0 : K)) + b ⊗ₜ[K] ((0 : K), (1 : K)))) = a := by
    rw [map_add (f := _), LinearMap.lTensor_tmul, LinearMap.lTensor_tmul, LinearMap.fst_apply, LinearMap.fst_apply,
      map_add, TensorProduct.rid_tmul, TensorProduct.rid_tmul, one_smul, zero_smul, add_zero]
  have hb : TensorProduct.rid K A
      ((LinearMap.snd K K K).lTensor A
        (a ⊗ₜ[K] ((1 : K), (0 : K)) + b ⊗ₜ[K] ((0 : K), (1 : K)))) = b := by
    rw [map_add (f := _), LinearMap.lTensor_tmul, LinearMap.lTensor_tmul, LinearMap.snd_apply, LinearMap.snd_apply,
      map_add, TensorProduct.rid_tmul, TensorProduct.rid_tmul, one_smul, zero_smul, zero_add]
  rw [hx0, map_zero, map_zero] at ha hb
  exact ⟨ha.symm, hb.symm⟩

theorem coords_unique : ∀ (D : D7) (v : Pl D) (w : D.host.E), (∀ f : D.host.F, algebraMap D.host.F D.host.E f ≠ w) →
    ∀ a b : Fv D.host.F v, a ⊗ₜ[D.host.F] (1 : D.host.E) + b ⊗ₜ[D.host.F] w = 0 → a = 0 ∧ b = 0 :=
  fun _ _ w hw a b h => coords_unique_of_field w hw a b h

end GlobalTheory.CoordUnique
