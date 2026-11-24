module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormPeriodSq
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Hilbert90IntegralIdelesOfMovedPrimes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicUnitaryCharacterTrivialAtNonsplitPlace
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardLatticeDoubleCosetClassesStabilisers
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPrimeIffNonSplitPlaceIdempotent
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAdelicPointUnitaryGroupGramOne
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepLatticeStabilizerVacuumEqDetCharSmul
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaCosetIndicatorReadingSphericalOffModulus
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsDual
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Levelaf
public import Formalism.SatakeDualWeyl.Statement
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Classical
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Int.Order
public import Init.Data.Nat.Basic
public import Init.Data.Nat.Coprime
public import Init.Data.Nat.Div.Basic
public import Init.Data.Nat.Gcd
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Divisibility.Basic
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.Group.Units.Basic
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.Ring.Cast
public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Union
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Int.Cast.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Int.Cast.Lemmas
public import Mathlib.Data.Int.GCD
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Factorization.Induction
public import Mathlib.Data.Nat.Find
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Nat.PrimeFin
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Lattice
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

open NumberField IsDedekindDomain
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.InertCofinite

open Matrix TensorProduct Formalism.UG Formalism.UG.P Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum.VacInt

theorem eps_dvd_nat (D : D7) (P : ℕ → Prop) (n : ℕ) (hn : n ≠ 0) (h : ∀ q : ℕ, q.Prime → q ∣ n → ¬ P q) :
    ∃ t ∈ OhE D, eps D.host.E P = (n : AE D) * t := by
  induction n using Nat.recOnMul with
  | zero => exact absurd rfl hn
  | one => exact ⟨_, eps_mem P, by simp⟩
  | prime p hp =>
    obtain ⟨s, hs, e⟩ := eps_dvd (E := D.host.E) P hp (h p hp dvd_rfl) 1
    exact ⟨s, hs, by simpa using e⟩
  | mul a b ha hb =>
    obtain ⟨s, hs, es⟩ := ha (left_ne_zero_of_mul hn) fun q hq hd => h q hq (hd.mul_right _)
    obtain ⟨t, ht, et⟩ := hb (right_ne_zero_of_mul hn) fun q hq hd => h q hq (hd.mul_left _)
    refine ⟨s * t, mul_mem hs ht, ?_⟩
    rw [← eps_idem P]
    conv_lhs => enter [1]; rw [es]
    rw [et]
    push_cast
    ring

theorem exists_denom (D : D7) (y : AE D) : ∃ n : ℕ, 0 < n ∧ (n : AE D) * y ∈ OhE D := by
  obtain ⟨d, hd0, hd⟩ := levelaf_denom (F := ℚ) y
  obtain ⟨z, rfl⟩ : ∃ z : ℤ, d = z := ⟨Rat.ringOfIntegersEquiv d, by
    apply Rat.ringOfIntegersEquiv.injective; simp⟩
  have hz : z.natAbs ≠ 0 := by rintro h; apply hd0; simp [Int.natAbs_eq_zero.1 h]
  have hC : levelafC (F := ℚ) D.host.E (z : 𝓞 ℚ) = (z : AE D) := by
    rw [levelafC, map_intCast]
    exact map_intCast (Algebra.TensorProduct.includeRight : _ →ₐ[ℚ] AE D) z
  refine ⟨z.natAbs, Nat.pos_of_ne_zero hz, ?_⟩
  rw [hC] at hd
  rcases Int.natAbs_eq z with e | e
  · rw [e] at hd; simpa [OhE] using hd
  · rw [e] at hd
    have := neg_mem hd
    simpa [OhE] using this

theorem exists_denom_zeroAt (D : D7) (y : AE D) :
    ∃ n : ℕ, 0 < n ∧ (n : AE D) * y ∈ OhE D ∧ ∀ q : ℕ, q.Prime → q ∣ n → ¬ ZeroAt D q y := by
  have hex := exists_denom D y
  obtain ⟨h0, h1⟩ := Nat.find_spec hex
  refine ⟨Nat.find hex, h0, h1, fun q hq hd hz => ?_⟩
  obtain ⟨m, hm, hc, s, hs, e⟩ := hz 0
  rw [pow_zero, one_mul] at e
  have hm' : (m : AE D) * y ∈ OhE D := e ▸ hs
  have hg : ((Nat.gcd (Nat.find hex) m : ℕ) : AE D) * y ∈ OhE D := by
    have := congrArg (Int.cast : ℤ → AE D) (Nat.gcd_eq_gcd_ab (Nat.find hex) m)
    push_cast at this
    rw [this]
    convert add_mem (mul_mem (intCast_mem (OhE D) (Nat.gcdA (Nat.find hex) m)) h1)
      (mul_mem (intCast_mem (OhE D) (Nat.gcdB (Nat.find hex) m)) hm') using 1
    ring
  have hle := Nat.find_min' hex ⟨Nat.gcd_pos_of_pos_left _ h0, hg⟩
  have heq : Nat.gcd (Nat.find hex) m = Nat.find hex := le_antisymm (Nat.gcd_le_left _ h0) hle
  have : q ∣ m := hd.trans (heq ▸ Nat.gcd_dvd_right _ _)
  exact (Nat.Prime.coprime_iff_not_dvd hq).1 hc.symm this

theorem intG_of_entries (D : D7) {N : ℕ} (g : GA D N)
    (h : ∀ i j, ((g : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) i j ∈ OhE D) :
    IntG D (g : GL (Fin N) (AE D)) := by
  have hg : cT (sgA D) ((g : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) *
      (1 : Matrix (Fin N) (Fin N) D.host.E).map (inc D) * (g : GL (Fin N) (AE D)) =
      (1 : Matrix (Fin N) (Fin N) D.host.E).map (inc D) := g.2
  rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one] at hg
  intro i j
  refine ⟨h i j, ?_⟩
  rw [Units.inv_eq_of_mul_eq_one_left hg]
  exact csDual_sig_mem _ (h j i)

theorem intG_part_cofinite {D : D7} {N : ℕ} (y : GA D N) (hy : SuppInert D (y : GL (Fin N) (AE D))) :
    ∃ s : Finset ℕ, (∀ p ∈ s, p.Prime ∧ InertQ D p) ∧
      IntG D (part D (fun p => p ∉ s) y : GL (Fin N) (AE D)) := by
  choose n h0 h1 h2 using fun ij : Fin N × Fin N => exists_denom_zeroAt D
    (((y : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) ij.1 ij.2 - (1 : Matrix (Fin N) (Fin N) (AE D)) ij.1 ij.2)
  refine ⟨Finset.univ.biUnion fun ij => (n ij).primeFactors, fun p hp => ?_, intG_of_entries D _ fun i j => ?_⟩
  · obtain ⟨ij, -, hp⟩ := Finset.mem_biUnion.1 hp
    have hq := Nat.prime_of_mem_primeFactors hp
    refine ⟨hq, ?_⟩
    by_contra hi
    exact h2 ij p hq (Nat.dvd_of_mem_primeFactors hp) (hy p hq hi ij.1 ij.2)
  · obtain ⟨t, ht, e⟩ := eps_dvd_nat D (fun p => p ∉ Finset.univ.biUnion fun ij => (n ij).primeFactors) (n (i, j))
      (h0 _).ne' fun q hq hd hn => hn (Finset.mem_biUnion.2 ⟨(i, j), Finset.mem_univ _,
        Nat.mem_primeFactors.2 ⟨hq, hd, (h0 _).ne'⟩⟩)
    have := add_mem (mul_mem ht (h1 (i, j))) (one_entry_mem (OhE D) i j)
    convert this using 1
    show cutM _ _ _ i j = _
    rw [cutM_apply, e]
    ring

end GlobalTheory.InertCofinite
