module

public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.ParConsts
public import Formalism.SharpRestriction.GlobalSchurBounds.TaylorLogMetric
public import Formalism.SharpRestriction.GrowthBounds.FormalGroupSystem
public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
public import Formalism.SharpRestriction.GlobalSchurBounds.FirstClaimLemmaTwoFourOfLemmaTwoThree
public import Formalism.SharpRestriction.DesignExistsOfChoices
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.EqOfLeOfAbsNormEq
public import Formalism.DirichletDensity.DirichletDensityProofs.QuadDiscr
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.Params
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Int.Lemmas
public import Init.Data.Int.Order
public import Init.Data.Nat.Basic
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.CharP.IntermediateField
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Irreducible.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Rat
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Degree.Operations
public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Algebra.Squarefree.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Rat.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.FieldTheory.KummerPolynomial
public import Mathlib.FieldTheory.Minpoly.Basic
public import Mathlib.FieldTheory.Minpoly.Field
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.BoundedOrder.Basic
public import Mathlib.Order.CompleteLattice.Defs
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal

@[expose] public section

namespace Formalism.MainNotions.Ext

open Polynomial Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.MainNotions.UnusedSlot33.HK

variable {R : Ranks} (H : Host R)

theorem exists_gen_K : ∃ x : H.K, x ^ 2 = ((-(H.d : ℤ) : ℤ) : H.K) ∧ IntermediateField.adjoin ℚ {x} = ⊤ := by
  have hb2 : H.sqd ^ 2 = ((-(H.d : ℤ) : ℤ) : H.E) := by
    push_cast
    exact H.sqd_sq
  obtain ⟨x, hxdef⟩ : ∃ x : H.K, (x : H.E) = H.sqd :=
    ⟨⟨H.sqd, IntermediateField.mem_adjoin_simple_self ℚ _⟩, rfl⟩
  refine ⟨x, ?_, gen_top H x hxdef⟩
  apply Subtype.ext
  push_cast
  rw [hxdef, hb2]
  push_cast
  rfl

theorem finrank_K : Module.finrank ℚ H.K = 2 := by
  obtain ⟨x, hx, hadj⟩ := exists_gen_K H
  have hd := H.hyp.2.1
  have hsf : Squarefree (-(H.d : ℤ)) := by
    rw [← Int.squarefree_natAbs, Int.natAbs_neg, Int.natAbs_natCast]
    exact hd.squarefree
  have h1 : (-(H.d : ℤ)) ≠ 1 := by omega
  have hirr : Irreducible (X ^ 2 - C ((-(H.d : ℤ) : ℤ) : ℚ)) :=
    X_pow_sub_C_irreducible_of_prime Nat.prime_two (Formalism.HF.P.quad_not_sq_rat _ hsf h1)
  have hmon : (X ^ 2 - C ((-(H.d : ℤ) : ℤ) : ℚ)).Monic := monic_X_pow_sub_C _ two_ne_zero
  have hev : aeval x (X ^ 2 - C ((-(H.d : ℤ) : ℤ) : ℚ)) = 0 := by simp [hx]
  have hmin : minpoly ℚ x = X ^ 2 - C ((-(H.d : ℤ) : ℤ) : ℚ) :=
    (minpoly.eq_of_irreducible_of_monic hirr hev hmon).symm
  have := IntermediateField.adjoin.finrank (K := ℚ) (x := x) (.of_finite ℚ x)
  rw [hmin, natDegree_X_pow_sub_C _, hadj, IntermediateField.finrank_top'] at this
  exact this


end Formalism.MainNotions.Ext
