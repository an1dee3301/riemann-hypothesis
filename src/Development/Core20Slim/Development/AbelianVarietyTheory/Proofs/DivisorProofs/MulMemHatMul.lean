module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsApprox
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilOperatorFixesCosetVector
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardLatticeDoubleCosetClassesStabilisers
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstStandardPairMemberHasThetaFunction
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

namespace GlobalTheory.HatProductMembership

open NumberField Formalism.BasicNotions Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.FunObj.SqNum

theorem mul_mem_hat_mul {D : D7} {I J : Ideal (𝓞 D.host.E)} {x y : AE D}
    (hx : x ∈ hatId D I) (hy : y ∈ hatId D J) : x * y ∈ hatId D (I * J) := by
  unfold hatId at hx hy ⊢
  induction hx using AddSubgroup.closure_induction with
  | mem a ha =>
    obtain ⟨u, hu, s, hs, rfl⟩ := ha
    induction hy using AddSubgroup.closure_induction with
    | mem b hb =>
      obtain ⟨v, hv, t, ht, rfl⟩ := hb
      refine AddSubgroup.subset_closure
        ⟨u * v, Ideal.mul_mem_mul hu hv, s * t, (OhE D).mul_mem hs ht, ?_⟩
      have h : ((u * v : 𝓞 D.host.E) : D.host.E) = (u : D.host.E) * (v : D.host.E) := rfl
      rw [h, map_mul]
      ring
    | zero => rw [mul_zero]; exact zero_mem _
    | add b c _ _ h1 h2 => rw [mul_add]; exact add_mem h1 h2
    | neg b _ h => rw [mul_neg]; exact neg_mem h
  | zero => rw [zero_mul]; exact zero_mem _
  | add a b _ _ h1 h2 => rw [add_mul]; exact add_mem h1 h2
  | neg a _ h => rw [neg_mul]; exact neg_mem h

end GlobalTheory.HatProductMembership
