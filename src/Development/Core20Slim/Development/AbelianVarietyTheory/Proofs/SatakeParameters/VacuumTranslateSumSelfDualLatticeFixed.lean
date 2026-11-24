module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.SatakeParameters.SelfDualOne
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeModelVacuumTranslateClassesIndependent
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.SatakeParameters.MulSelfEqOneIffOfLinearOrderedCommGroupWithZero
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalThetaPairExistence
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemIntMat
public import Formalism.SatakeDualWeyl.Statement
public import Formalism.SatakeDualWeyl.StatementF
public import Init.Classical
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.WithOne.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.GroupWithZero.Units.Lemmas
public import Mathlib.Algebra.GroupWithZero.WithZero
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Order.Monoid.Unbundled.TypeTags
public import Mathlib.Algebra.Quotient
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Algebra.Torsor.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.NNRat.Defs
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Rat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Logic.Function.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.RingTheory.Valuation.Integers
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Valued.ValuationTopology
public import Mathlib.Topology.UniformSpace.Cauchy

@[expose] public section

open Matrix

namespace GlobalTheory.Hk3.HoweG

theorem vacuum_sum_selfDual_fixed : ∀ (L : Type) [Field L] [CharZero L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L)
    (n n' : ℕ) (JS : GL (Fin n) L) (JT : GL (Fin n') L) (ψ : AddChar L ℂ) (M : Type) [AddCommGroup M] [Module ℂ M]
    (ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M)
    (ω : Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L) × Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L) →* Module.End ℂ M),
    GlobalTheory.Hk3.LocPair ϖ σ q δ JS JT ψ ρ ω → ∀ s : M, GlobalTheory.Hk3.LocVac ρ s →
    ∀ a : GL (Fin n) L, GlobalTheory.Hk3.HoweG.SelfDual σ JS a → ∀ Z : Finset (Matrix (Fin n') (Fin n) L),
    (∀ z ∈ Z, ∃ u : Matrix (Fin n') (Fin n) L, (∀ i j, u i j ∈ Formalism.UG.intL L) ∧
      z = u * ((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) →
    (∀ z ∈ Z, ∀ z' ∈ Z, z - z' ∈ GlobalTheory.Hk3.HoweDuality.intMat L n' n → z = z') →
    (∀ u : Matrix (Fin n') (Fin n) L, (∀ i j, u i j ∈ Formalism.UG.intL L) →
      ∃ z ∈ Z, u * ((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) - z ∈ GlobalTheory.Hk3.HoweDuality.intMat L n' n) →
    ∀ u : Matrix (Fin n') (Fin n) L, (∀ i j, u i j ∈ Formalism.UG.intL L) →
      ρ (u * ((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) (∑ z ∈ Z, ρ z s) = ∑ z ∈ Z, ρ z s := by
  intro L _ _ _ _ ϖ σ q δ n n' JS JT ψ M _ _ ρ ω hP s hvac a hSD Z hZform hZdist hZcov u hu
  classical
  obtain ⟨hU, hodd, hSint, hTint, -, -, hδ, hpsi, -, -, hρ, -, -, -⟩ := hP
  have hσσ := hU.1
  have hσv := hU.2.1
  have h2 : Valued.v (2 : L) = 1 := GlobalTheory.Hk3.Inh.v_two hU hodd
  set A : Matrix (Fin n) (Fin n) L := ((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) with hA
  set P : Matrix (Fin n) (Fin n) L := ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) with hPdef

  have hloc : ∀ w w' : Matrix (Fin n') (Fin n) L, (∀ i j, w i j ∈ Formalism.UG.intL L) → (∀ i j, w' i j ∈ Formalism.UG.intL L) →
      locH σ δ JS JT (w * A) (w' * A) ∈ Formalism.UG.intL L := by
    intro w w' hw hw'
    have hw'σ : ∀ i j, (w'.map σ)ᵀ i j ∈ Formalism.UG.intL L := by
      intro i j
      show Valued.v (σ (w' j i)) ≤ 1
      rw [hσv]; exact hw' j i
    have hJT : ∀ i j, (JT : Matrix (Fin n') (Fin n') L) i j ∈ Formalism.UG.intL L := fun i j => glint_entry hTint i j
    have hB : ∀ i j, (A * P * (A.map σ)ᵀ) i j ∈ Formalism.UG.intL L := hSD.2
    have hC : ∀ i j, ((w'.map σ)ᵀ * (JT : Matrix (Fin n') (Fin n') L) * w) i j ∈ Formalism.UG.intL L :=
      matMul_int (matMul_int hw'σ hJT) hw
    have e : locH σ δ JS JT (w * A) (w' * A) =
        δ * Matrix.trace ((A * P * (A.map σ)ᵀ) * ((w'.map σ)ᵀ * (JT : Matrix (Fin n') (Fin n') L) * w)) := by
      unfold locH
      congr 1
      rw [Matrix.map_mul, Matrix.transpose_mul]
      calc Matrix.trace (P * ((A.map σ)ᵀ * (w'.map σ)ᵀ) * (JT : Matrix (Fin n') (Fin n') L) * (w * A))
          = Matrix.trace ((P * (A.map σ)ᵀ * (w'.map σ)ᵀ * (JT : Matrix (Fin n') (Fin n') L) * w) * A) := by
            simp only [Matrix.mul_assoc]
        _ = Matrix.trace (A * (P * (A.map σ)ᵀ * (w'.map σ)ᵀ * (JT : Matrix (Fin n') (Fin n') L) * w)) :=
            Matrix.trace_mul_comm _ _
        _ = _ := by simp only [Matrix.mul_assoc]
    rw [e]
    refine (Formalism.UG.intL L).mul_mem (le_of_eq hδ.1) ?_
    unfold Matrix.trace
    exact (Formalism.UG.intL L).sum_mem fun i _ => matMul_int hB hC i i

  have hpair : ∀ w w' : Matrix (Fin n') (Fin n) L, (∀ i j, w i j ∈ Formalism.UG.intL L) → (∀ i j, w' i j ∈ Formalism.UG.intL L) →
      ψ ((locH σ δ JS JT (w * A) (w' * A) + σ (locH σ δ JS JT (w * A) (w' * A))) / 2) = 1 := by
    intro w w' hw hw'
    have hcI := hloc w w' hw hw'
    have hσc : σ (locH σ δ JS JT (w * A) (w' * A)) ∈ Formalism.UG.intL L := by
      show Valued.v (σ _) ≤ 1
      rw [hσv]; exact hcI
    apply hpsi
    · rw [GlobalTheory.Hk3.mem_intL_iff, map_div₀, h2, div_one]
      exact (Formalism.UG.intL L).add_mem hcI hσc
    · rw [map_div₀, map_add (f := _), hσσ, map_ofNat]; ring
  have hcomb : ∀ w w' : Matrix (Fin n') (Fin n) L, (∀ i j, w i j ∈ Formalism.UG.intL L) → (∀ i j, w' i j ∈ Formalism.UG.intL L) →
      ∀ t : M, ρ (w * A) (ρ (w' * A) t) = ρ (w * A + w' * A) t := by
    intro w w' hw hw' t
    have := congrArg (fun f => f t) (hρ (w * A) (w' * A))
    simp only [Module.End.mul_apply, LinearMap.smul_apply] at this
    rw [this, hpair w w' hw hw', one_smul]
  have key : ∀ z ∈ Z, ∃ z' ∈ Z, ρ (u * A) (ρ z s) = ρ z' s ∧ (u * A + z) - z' ∈ GlobalTheory.Hk3.HoweDuality.intMat L n' n := by
    intro z hz
    obtain ⟨v, hv, rfl⟩ := hZform z hz
    have huv : ∀ i j, (u + v) i j ∈ Formalism.UG.intL L := fun i j => (Formalism.UG.intL L).add_mem (hu i j) (hv i j)
    obtain ⟨z', hz', hdiff⟩ := hZcov (u + v) huv
    obtain ⟨v', hv', rfl⟩ := hZform z' hz'
    refine ⟨v' * A, hz', ?_, by rwa [← Matrix.add_mul]⟩
    have hw : ∀ i j, (u + v - v') i j ∈ Formalism.UG.intL L := fun i j => (Formalism.UG.intL L).sub_mem (huv i j) (hv' i j)
    have hl : ρ ((u + v - v') * A) s = s := by
      apply hvac
      rw [Matrix.sub_mul]
      exact hdiff
    rw [hcomb u v hu hv]
    calc ρ (u * A + v * A) s = ρ (v' * A + (u + v - v') * A) s := by
          congr 1; rw [Matrix.sub_mul, Matrix.add_mul]; abel
      _ = ρ (v' * A) (ρ ((u + v - v') * A) s) := (hcomb v' _ hv' hw s).symm
      _ = ρ (v' * A) s := by rw [hl]
  choose! f hfZ hf hfd using key
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.sum_congr rfl hf]
  have hinj : ∀ x ∈ Z, ∀ y ∈ Z, f x = f y → x = y := by
    intro z1 h1 z2 h2 he
    apply hZdist z1 h1 z2 h2
    have := sub_mem (hfd z1 h1) (hfd z2 h2)
    rw [he] at this
    convert this using 1; abel
  have himg : Z.image f = Z := Finset.eq_of_subset_of_card_le
    (fun x hx => by obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx; exact hfZ z hz)
    (by rw [Finset.card_image_of_injOn (fun x hx y hy h => hinj x hx y hy h)])
  rw [← Finset.sum_image (f := fun z => ρ z s) hinj, himg]

end GlobalTheory.Hk3.HoweG
