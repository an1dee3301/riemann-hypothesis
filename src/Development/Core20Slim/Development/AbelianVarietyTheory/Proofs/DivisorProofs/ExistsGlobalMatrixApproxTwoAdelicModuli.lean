module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjSmulNeBot
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.VacuumUnderAdelicPairModulusOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CompletedStandardAdelicLatticeProperties
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsNormMulMemHatId
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Int.Lemmas
public import Init.Data.Nat.Basic
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Divisibility.Basic
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Order.Kleene
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.BoundedOrder.Basic
public import Mathlib.Order.CompleteLattice.Defs
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Maximal
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
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
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

namespace GlobalTheory.BotPairSmall.CongApprox

theorem approx_two_moduli : ∀ (D : D7) (𝔫 : Ideal (𝓞 D.host.E)), 𝔫 ≠ ⊥ → ∀ (a d : ℕ) (M : Matrix (Fin d) (Fin a) (AE D)) (m : ℕ), 0 < m → ∃ z : Matrix (Fin d) (Fin a) D.host.E, (∀ i l, ∃ y ∈ IhE D ⊤, (z.map (inc D) - M) i l = (m : AE D) * y) ∧ ∀ i l, (M - z.map (inc D)) i l ∈ hatId D 𝔫 := by
  intro D 𝔫 h𝔫 a d M m hm
  obtain ⟨n, hn, hnI⟩ := GlobalTheory.CompletedLattice.exists_mul_IhE_mem D ⊤
  have hN : 0 < Ideal.absNorm 𝔫 := Nat.pos_of_ne_zero (by rwa [Ne, Ideal.absNorm_eq_zero_iff])
  obtain ⟨z, hz⟩ := GlobalTheory.NormSum.VacMove.MI_approx (D := D) (cc := ⊤) top_ne_bot M (m * (n * Ideal.absNorm 𝔫))
    (Nat.mul_pos hm (Nat.mul_pos hn hN))
  refine ⟨z, GlobalTheory.NormSum.VacMove.MI.of_dvd (dvd_mul_right m _) hz, fun i l => ?_⟩
  obtain ⟨y, hy, e⟩ := hz i l
  have hny : (n : AE D) * y ∈ OhE D := hnI y hy
  have hmny : (m : AE D) * ((n : AE D) * y) ∈ OhE D := mul_mem (natCast_mem _ m) hny
  have h2 := GlobalTheory.BotPairSmall.BlockIdx.absNorm_mul_mem_hatId D 𝔫 hmny
  have e2 : (M - z.map (inc D)) i l = -((Ideal.absNorm 𝔫 : AE D) * ((m : AE D) * ((n : AE D) * y))) := by
    rw [← neg_sub, Matrix.neg_apply, e]; push_cast; ring
  rw [e2]
  exact neg_mem h2

end GlobalTheory.BotPairSmall.CongApprox
