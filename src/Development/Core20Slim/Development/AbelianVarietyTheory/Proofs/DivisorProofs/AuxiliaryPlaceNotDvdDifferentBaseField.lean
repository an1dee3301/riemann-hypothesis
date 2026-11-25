module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitaryOnTheta
public import Development.AbelianVarietyTheory.Definitions.Divisors.LeastSplitAuxiliaryPrimeThetaChainSpec
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataParams
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.SharpRestriction.LevelLetterCocycles.TwGood
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Int.Gcd
public import Init.Data.Int.Linear
public import Init.Data.Int.Order
public import Init.Data.Nat.Basic
public import Init.Data.Nat.Coprime
public import Init.Data.Nat.Div.Basic
public import Init.Data.Nat.Dvd
public import Init.Data.Nat.Gcd
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.AffineMonoid.Basic
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Divisibility.Basic
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Module.Torsion.Free
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.NoZeroSMulDivisors.Basic
public import Mathlib.Algebra.NoZeroSMulDivisors.Defs
public import Mathlib.Algebra.Order.Kleene
public import Mathlib.Algebra.Ring.CharZero
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Basic
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Basic
public import Mathlib.Data.Int.Cast.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Mathlib.NumberTheory.NumberField.Discriminant.Different
public import Mathlib.Order.Basic
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.Coprime.Basic
public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.DedekindDomain.Different
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Lattice
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Ideal.Prime
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField
open GlobalTheory.ChiGrid GlobalTheory.SqTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DifferentAtBasePlace

theorem ne_of_mod_eq_one' {p M k : ℕ} (hp : p % M = 1) (hk : k ∣ M) (hk1 : 1 < k) : p ≠ k := by
  rintro rfl
  have h := Nat.mod_mod_of_dvd p hk
  rw [hp, Nat.mod_self, Nat.mod_eq_of_lt hk1] at h
  exact one_ne_zero h

theorem natAbs_discr_F_dvd (D : D7) : (discr D.host.F).natAbs ∣ (discr D.host.E).natAbs := by
  rw [natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow D.host.F (𝓞 D.host.F) D.host.E (𝓞 D.host.E)]
  exact Dvd.dvd.mul_left (dvd_pow_self _ Module.finrank_pos.ne') _

theorem leastSplitAuxiliaryPrime_not_dvd_discr_base (D : D7) : ¬ q0 D ∣ (discr D.host.F).natAbs := by
  obtain ⟨hp, hm, -⟩ := leastSplitAuxiliaryPrimeThetaChain_spec D
  intro h
  have hc : q0 D ∣ Formalism.BasicNotions.LevelStarExponents.condE D :=
    D.host.der.discr_primes.1 _ hp (Int.natCast_dvd.2 (h.trans (natAbs_discr_F_dvd D)))
  exact ne_of_mod_eq_one' hm (dvd_mul_of_dvd_right hc _) hp.one_lt rfl

theorem not_dvd_different {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc) :
    ¬ G.pl.v0.asIdeal ∣ differentIdeal ℤ (𝓞 D.host.F) := by
  intro h
  have hdisc : ((discr D.host.F : ℤ) : 𝓞 D.host.F) ∈ G.pl.v0.asIdeal :=
    Ideal.le_of_dvd h (discr_mem_differentIdeal D.host.F (𝓞 D.host.F))
  have hq : ((q0 D : ℕ) : 𝓞 D.host.F) ∈ G.pl.v0.asIdeal := G.pl.basePlace_over_qZero
  have hcop : IsCoprime (q0 D : ℤ) (discr D.host.F) := by
    rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_comm, Int.gcd, Int.natAbs_natCast]
    exact Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd (leastSplitAuxiliaryPrimeThetaChain_spec D).1).2 (leastSplitAuxiliaryPrime_not_dvd_discr_base D))
  obtain ⟨u, v, huv⟩ := hcop
  apply G.pl.v0.isPrime.ne_top
  rw [Ideal.eq_top_iff_one]
  have := congrArg (Int.cast : ℤ → 𝓞 D.host.F) huv
  push_cast at this
  rw [← this]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (by exact_mod_cast hq)) (Ideal.mul_mem_left _ _ hdisc)

end GlobalTheory.DifferentAtBasePlace
