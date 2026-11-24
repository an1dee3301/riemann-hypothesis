module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetVecEq
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.WeilOperatorRationalTranslateMemThetaFunctions
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Int.Lemmas
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Basic
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Order.Group.Action
public import Mathlib.Algebra.Order.Kleene
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Ring.Action.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.BoundedOrder.Basic
public import Mathlib.Order.BoundedOrder.Lattice
public import Mathlib.Order.CompleteLattice.Defs
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.DedekindDomain.Different
public import Mathlib.RingTheory.DedekindDomain.Ideal.Basic
public import Mathlib.RingTheory.FractionalIdeal.Basic
public import Mathlib.RingTheory.FractionalIdeal.Operations
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Maximal
public import Mathlib.RingTheory.Ideal.Pointwise

@[expose] public section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)
open scoped nonZeroDivisors

namespace GlobalTheory.FunObj.SqNum

theorem pt_mem_of_entries_mem (D : D7) (δ : ℂ) (𝔪 : Ideal (𝓞 D.host.E)) {a d : ℕ}
    (w : Matrix (Fin d) (Fin a) D.host.E) (hw : ∀ i j, ∃ b ∈ 𝔪, w i j = (b : D.host.E)) :
    pt D (tor0 D ⊤ δ) δ w ∈ La0 D (tor0 D ⊤ δ) a d ∧
      pt D (tor0 D ⊤ δ) δ w ∈ La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d) := by
  have key : ∀ L' : Submodule (𝓞 D.host.E) (Fin d → D.host.E), (∀ x ∈ stdL D a, w.mulVec x ∈ L') →
      pt D (tor0 D ⊤ δ) δ w ∈ La D (tor0 D ⊤ δ) (stdL D a) L' := by
    intro L' hL'
    refine AddSubgroup.subset_closure ⟨δ, AddSubgroup.subset_closure ⟨1, trivial, by simp⟩, w, ?_, rfl⟩
    refine Submodule.subset_span ⟨1, ?_, w, Submodule.subset_span hL', (one_smul _ _).symm⟩
    refine FractionalIdeal.one_mem_inv_coe_ideal fun h => ?_
    have h2 := D.host.𝔟_spec.2
    rw [h, Ideal.smul_bot, sup_bot_eq] at h2
    exact bot_ne_top h2
  have hent : ∀ x ∈ stdL D a, ∀ i, w.mulVec x i ∈
      ((𝔪 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) : Submodule (𝓞 D.host.E) D.host.E) := by
    intro x hx i
    show ∑ j, w i j * x j ∈ _
    refine Submodule.sum_mem _ fun j _ => ?_
    obtain ⟨b, hb, hbw⟩ := hw i j
    obtain ⟨y, hy⟩ := Submodule.mem_one.1 (hx j trivial)
    refine (FractionalIdeal.mem_coeIdeal _).2 ⟨b * y, 𝔪.mul_mem_right y hb, ?_⟩
    rw [hbw, ← hy, map_mul]
  refine ⟨key _ fun x hx i _ => ?_, key _ fun x hx i _ => ?_⟩
  · have := (FractionalIdeal.coe_le_coe.2 FractionalIdeal.coeIdeal_le_one) (hent x hx i)
    rw [FractionalIdeal.coe_one] at this
    exact this
  · by_cases h𝔪 : 𝔪 = ⊥
    · have := hent x hx i
      rw [h𝔪, FractionalIdeal.coeIdeal_bot] at this
      have h0 : w.mulVec x i = 0 := by simpa using this
      rw [h0]
      exact zero_mem _
    · have hne : ((D.host.conj • 𝔪 : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≠ 0 := by
        rw [Ne, FractionalIdeal.coeIdeal_eq_zero]
        intro h
        apply h𝔪
        have := congrArg (fun J : Ideal (𝓞 D.host.E) => D.host.conj⁻¹ • J) h
        simpa using this
      have hle : (𝔪 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≤
          (𝔪 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) /
            ((D.host.conj • 𝔪 : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) := by
        rw [FractionalIdeal.le_div_iff_mul_le hne]
        first
        | exact mul_le_of_le_one_right' FractionalIdeal.coeIdeal_le_one
        | exact mul_le_of_le_one_right (zero_le _) FractionalIdeal.coeIdeal_le_one
        | exact (mul_le_mul_left FractionalIdeal.coeIdeal_le_one _).trans_eq (mul_one _)
        | exact (FractionalIdeal.mul_le_mul_left FractionalIdeal.coeIdeal_le_one _).trans_eq (mul_one _)
        | exact (mul_le_mul_of_nonneg_left FractionalIdeal.coeIdeal_le_one (zero_le _)).trans_eq (mul_one _)
      exact (FractionalIdeal.coe_le_coe.2 hle) (hent x hx i)

end GlobalTheory.FunObj.SqNum
