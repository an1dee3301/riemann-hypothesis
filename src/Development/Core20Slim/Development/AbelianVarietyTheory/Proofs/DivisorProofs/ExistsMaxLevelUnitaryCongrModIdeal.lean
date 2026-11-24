module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdempotentLimitPowersIntegralAdeles
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralUnitaryGlueIdempotent
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOrthogonalIdempotentDivisibleCongruent
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUnitaryExtension
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Order.Kleene
public import Mathlib.Algebra.Quotient
public import Mathlib.Algebra.Ring.Action.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Pointwise
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open GlobalTheory.FunObj.SqNum GlobalTheory.NormSum

noncomputable section

namespace GlobalTheory.MaxLevelLift

theorem exists_intG_cong : ∀ (D : D7) (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ≠ ⊥ → 𝔪 ⊔ D.host.conj • 𝔪 = ⊤ → ∀ (N : ℕ)
    (g : Matrix (Fin N) (Fin N) (𝓞 D.host.E)), IsUnit (g.map (Ideal.Quotient.mk 𝔪)).det →
      ∃ k : GA D N, k ∈ intG D N ∧ ∀ i j : Fin N,
        ((k : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) i j - inc D ((g i j : 𝓞 D.host.E) : D.host.E) ∈ hatId D 𝔪 := by
  intro D 𝔪 _ hcop N g hg
  have hcc : D.host.conj * D.host.conj = 1 := AlgEquiv.ext fun z => GlobalTheory.NormSum.UnramHecke.conj_conj D z
  have e : D.host.conj • D.host.conj • 𝔪 = 𝔪 := by rw [smul_smul, hcc, one_smul]
  have hdet : (g.map (Ideal.Quotient.mk 𝔪)).det = Ideal.Quotient.mk 𝔪 g.det :=
    ((Ideal.Quotient.mk 𝔪).map_det g).symm
  rw [hdet] at hg
  obtain ⟨v, hv⟩ := hg.exists_right_inv
  obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective v
  rw [← map_mul, ← map_one (Ideal.Quotient.mk 𝔪), Ideal.Quotient.eq] at hv
  have key : inc D ((g.det * u : 𝓞 D.host.E) : D.host.E) - 1 ∈ hatId D (D.host.conj • D.host.conj • 𝔪) := by
    rw [e]
    exact AddSubgroup.subset_closure ⟨g.det * u - 1, hv, 1, one_mem _, by simp⟩
  obtain ⟨f, hf, w, hw, hff, hfs, hfw, h1f⟩ :=
    GlobalTheory.BotPairSmall.IdemChoice.exists_idem_of_limit GlobalTheory.AlgIntIdem.idem D (D.host.conj • 𝔪)
      (by rw [e, sup_comm]; exact hcop) _ _ key
  rw [e] at h1f
  obtain ⟨k, hk, hkc⟩ := GlobalTheory.GlueUnitary.glue_unitary D 𝔪 N g f w hf hw hff hfs hfw h1f
  refine ⟨k⁻¹, inv_mem hk, fun i j => ?_⟩
  have := neg_mem (hkc i j)
  rwa [Matrix.sub_apply, neg_sub, Matrix.map_apply] at this

end GlobalTheory.MaxLevelLift
