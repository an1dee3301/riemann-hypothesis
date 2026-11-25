module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetVecEq
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmFiniteAdeleStrongApproxModAdelicIdeal
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Adelstab
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlob
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Classical
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Lattice
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
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Mathlib.RingTheory.NonUnitalSubring.Defs
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Tactic.LinearCombination.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

noncomputable section

namespace GlobalTheory.FunObj.CosetApprox

theorem exists_mem_approx (D : D7) (𝔪 : Ideal (𝓞 D.host.E)) (m : ℕ) (hm : 0 < m) (y : AE D)
    (hy : y ∈ hatId D 𝔪) : ∃ b ∈ 𝔪, ∃ t ∈ IhE D ⊤, inc D (b : D.host.E) - y = (m : AE D) * t := by
  induction hy using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨b, hb, s, hs, rfl⟩ := hx
    obtain ⟨r, w, hw, e⟩ := GlobalTheory.AdelicApprox.exists_approx D m hm s hs
    have hr : inc D r ∈ OhE D := by
      have : inc D r = s - (m : AE D) * w := by rw [e]; ring
      rw [this]
      exact sub_mem hs (mul_mem (natCast_mem _ m) hw)
    have hri : IsIntegral ℤ r := Formalism.UG.P.csGlob_int (F := ℚ) _ hr
    let r' : 𝓞 D.host.E := ⟨r, hri⟩
    have hbr : b * r' ∈ 𝔪 := Ideal.mul_mem_right _ _ hb
    have hbw : inc D (b : D.host.E) * w ∈ OhE D := mul_mem (Formalism.UG.P.adelstab_incl_int b) hw
    refine ⟨b * r', hbr, -(inc D (b : D.host.E) * w), neg_mem ?_, ?_⟩
    · have := GlobalTheory.AdelicApprox.absNorm_mul_mem_IhE D ⊤ _ hbw
      simpa using this
    · have hc : ((b * r' : 𝓞 D.host.E) : D.host.E) = (b : D.host.E) * r := rfl
      rw [hc, map_mul, e]
      ring
  | zero => exact ⟨0, zero_mem _, 0, zero_mem _, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨b, hb, t, ht, e⟩ := hx
    obtain ⟨b', hb', t', ht', e'⟩ := hy
    refine ⟨b + b', add_mem hb hb', t + t', add_mem ht ht', ?_⟩
    push_cast
    rw [map_add (f := _)]
    linear_combination e + e'
  | neg x _ hx =>
    obtain ⟨b, hb, t, ht, e⟩ := hx
    refine ⟨-b, neg_mem hb, -t, neg_mem ht, ?_⟩
    push_cast
    rw [map_neg]
    linear_combination -e

theorem matrix_approx : ∀ (D : D7) (𝔪 : Ideal (𝓞 D.host.E)) {a d : ℕ} (Y : Matrix (Fin d) (Fin a) (AE D)),
    (∀ i j, Y i j ∈ hatId D 𝔪) → ∀ m : ℕ, 0 < m → ∃ w : Matrix (Fin d) (Fin a) D.host.E,
      (∀ i j, ∃ b ∈ 𝔪, w i j = (b : D.host.E)) ∧ ∀ i j, ∃ y ∈ IhE D ⊤, (w.map (inc D) - Y) i j = (m : AE D) * y := by
  intro D 𝔪 a d Y hY m hm
  choose b hb t ht e using fun i j => exists_mem_approx D 𝔪 m hm (Y i j) (hY i j)
  refine ⟨Matrix.of fun i j => ((b i j : 𝓞 D.host.E) : D.host.E), fun i j => ⟨b i j, hb i j, rfl⟩,
    fun i j => ⟨t i j, ht i j, ?_⟩⟩
  simpa using e i j

end GlobalTheory.FunObj.CosetApprox
