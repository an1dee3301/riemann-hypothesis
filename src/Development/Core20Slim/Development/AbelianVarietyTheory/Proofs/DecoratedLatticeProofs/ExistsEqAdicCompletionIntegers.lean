module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsEqTransposeMulMapOfIdempotent
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FiniteResidueFieldAdicCompletionIntegers
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Lattice
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Tactic.LinearCombination.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

open IsDedekindDomain NumberField IsLocalRing

namespace GlobalTheory.BinaryUnitForm

theorem exists_eq_of_henselian {R : Type*} [CommRing R] [IsLocalRing R]
    [HenselianRing R (maximalIdeal R)] [Finite (ResidueField R)] (t n u : R)
    (hD : IsUnit (t ^ 2 - 4 * n)) (hu : IsUnit u) :
    ∃ r s : R, r ^ 2 + t * r * s + n * s ^ 2 = u := by
  obtain ⟨r, s, hrs⟩ := GlobalTheory.UnramifiedHermitian.exists_binary_eq_of_finite
    (a := residue R t) (n := residue R n)
    (by simpa only [map_sub, map_mul, map_pow, map_ofNat] using (hD.map (residue R)).ne_zero)
    (residue R u)
  obtain ⟨r, rfl⟩ := residue_surjective r
  obtain ⟨s, rfl⟩ := residue_surjective s
  have hN : residue R (r ^ 2 + t * r * s + n * s ^ 2) = residue R u := by
    simpa only [map_add (f := _), map_mul, map_pow] using hrs
  have hNu : IsUnit (r ^ 2 + t * r * s + n * s ^ 2) := by
    rw [← residue_ne_zero_iff_isUnit, hN]
    exact (hu.map _).ne_zero
  obtain ⟨w, hw⟩ := hNu.exists_right_inv
  have he : u * w - 1 ∈ maximalIdeal R := by
    rw [← residue_eq_zero_iff, map_sub, map_mul, ← hN, ← map_mul, hw, map_one, sub_self]

  have hspan : Ideal.span {(2 : R), t} = ⊤ := by
    apply Ideal.eq_top_of_isUnit_mem _ _ hD
    rw [Ideal.mem_span_pair]
    exact ⟨-2 * n, t, by ring⟩
  obtain ⟨α, β, hαβ⟩ := Ideal.mem_span_pair.1
    (show (1 : R) ∈ Ideal.span {(2 : R), t} by rw [hspan]; exact Submodule.mem_top)
  obtain ⟨T, hT⟩ := GlobalTheory.UnramifiedHermitian.exists_add_mul_sq_eq (maximalIdeal R)
    (α ^ 2 + t * α * β + n * β ^ 2) he
  refine ⟨r * (1 + T * α) - n * s * (T * β), r * (T * β) + (1 + T * α) * s + t * s * (T * β), ?_⟩
  linear_combination (r ^ 2 + t * r * s + n * s ^ 2) * T * hαβ
    + (r ^ 2 + t * r * s + n * s ^ 2) * hT + u * hw

theorem exists_eq_adicCompletionIntegers : ∀ (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (t n u : v.adicCompletionIntegers F),
    IsUnit (t ^ 2 - 4 * n) → IsUnit u → ∃ r s : v.adicCompletionIntegers F,
      r ^ 2 + t * r * s + n * s ^ 2 = u := by
  intro F _ _ v t n u hD hu
  haveI := GlobalTheory.SelfDualGenus.isAdicComplete_adicCompletionIntegers v
  haveI := GlobalTheory.SelfDualGenus.finite_residueField_adicCompletionIntegers v
  exact exists_eq_of_henselian t n u hD hu

end GlobalTheory.BinaryUnitForm
