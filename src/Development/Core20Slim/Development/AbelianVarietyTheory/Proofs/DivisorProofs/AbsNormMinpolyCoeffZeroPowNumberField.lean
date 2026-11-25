module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Formalism.PairingDivisors.StatementH
public import Batteries.Classes.RatCast
public import Init.Core
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.Hom.Rat
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.CharP.IntermediateField
public import Mathlib.Algebra.EuclideanDomain.Defs
public import Mathlib.Algebra.EuclideanDomain.Field
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Irreducible.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Rat
public import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Ring.Unbundled.Rat
public import Mathlib.Algebra.Order.Star.Rat
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Prime.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Algebra.Star.Rat
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Logic.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Rat.Cast.Defs
public import Mathlib.Data.Rat.Defs
public import Mathlib.Data.Set.CoeSort
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.FieldTheory.IntermediateField.Algebraic
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.FieldTheory.Minpoly.Basic
public import Mathlib.FieldTheory.Perfect
public import Mathlib.FieldTheory.Separable
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Lattice
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Algebraic.Defs
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.Norm.Basic
public import Mathlib.RingTheory.Norm.Defs
public import Mathlib.RingTheory.Norm.Transitivity
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.PowerBasis
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal

@[expose] public section

open NumberField Polynomial IsDedekindDomain
open Formalism.DivisionValues (vw lw)

namespace GlobalTheory.NormTower

open IntermediateField

theorem abs_norm_coeff_zero_pow (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (β : ℂ) (p : K[X])
    (h : GlobalTheory.FunObj.SqNum.IsMinPol σ β p) (hβ : IsAlgebraic ℚ β) :
    |(Algebra.norm ℚ (p.coeff 0) : ℚ)| ^ (minpoly ℚ β).natDegree =
      |(minpoly ℚ β).coeff 0| ^ (p.natDegree * Module.finrank ℚ K) := by
  obtain ⟨hm, hirr, hev⟩ := h
  haveI := Fact.mk hirr
  let pb := AdjoinRoot.powerBasis hirr.ne_zero
  haveI : Module.Finite K (AdjoinRoot p) := pb.finite
  haveI : FiniteDimensional ℚ (AdjoinRoot p) := Module.Finite.trans K (AdjoinRoot p)
  set r := AdjoinRoot.root p
  have hNK : Algebra.norm K r = (-1) ^ p.natDegree * p.coeff 0 := by
    have := Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly pb
    rwa [AdjoinRoot.minpoly_powerBasis_gen_of_monic hm, AdjoinRoot.powerBasis_gen, AdjoinRoot.powerBasis_dim] at this
  let φ : AdjoinRoot p →+* ℂ := AdjoinRoot.lift σ β hev
  have hφ : φ r = β := AdjoinRoot.lift_root hev
  have hmin : minpoly ℚ r = minpoly ℚ β := by
    rw [← hφ]; exact (minpoly.algHom_eq φ.toRatAlgHom φ.injective r).symm
  have hint : IsIntegral ℚ r := .of_finite ℚ r
  have h1 : Algebra.norm ℚ r = Algebra.norm ℚ ((-1) ^ p.natDegree * p.coeff 0 : K) := by
    rw [← hNK, Algebra.norm_norm]
  have h2 := Algebra.norm_eq_norm_adjoin ℚ r
  have h3 : Algebra.norm ℚ (IntermediateField.AdjoinSimple.gen ℚ r) =
      (-1) ^ (minpoly ℚ β).natDegree * (minpoly ℚ β).coeff 0 := by
    have := Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly (IntermediateField.adjoin.powerBasis hint)
    rw [IntermediateField.adjoin.powerBasis_gen hint, IntermediateField.minpoly_gen, IntermediateField.adjoin.powerBasis_dim, hmin] at this
    exact this
  have hdeg : Module.finrank ℚ (AdjoinRoot p) = p.natDegree * Module.finrank ℚ K := by
    rw [← Module.finrank_mul_finrank ℚ K (AdjoinRoot p), pb.finrank, AdjoinRoot.powerBasis_dim, mul_comm]
  have hdeg2 : Module.finrank ℚ (AdjoinRoot p) = (minpoly ℚ β).natDegree * Module.finrank ℚ⟮r⟯ (AdjoinRoot p) := by
    rw [← Module.finrank_mul_finrank ℚ ℚ⟮r⟯ (AdjoinRoot p), IntermediateField.adjoin.finrank hint, hmin]
  have hn1 : |Algebra.norm ℚ (-1 : K)| = 1 := by
    rw [show (-1 : K) = algebraMap ℚ K (-1) by simp, Algebra.norm_algebraMap]; simp
  have key : |Algebra.norm ℚ (p.coeff 0)| = |(minpoly ℚ β).coeff 0| ^ Module.finrank ℚ⟮r⟯ (AdjoinRoot p) := by
    have e := congrArg abs (h1.symm.trans (h2.trans (congrArg (· ^ Module.finrank ℚ⟮r⟯ (AdjoinRoot p)) h3)))
    rw [map_mul, map_pow, abs_mul, abs_pow, hn1, one_pow, one_mul, abs_pow, abs_mul, abs_pow, abs_neg, abs_one, one_pow,
      one_mul] at e
    exact e
  rw [key, ← pow_mul, mul_comm, ← hdeg2, hdeg]

end GlobalTheory.NormTower
