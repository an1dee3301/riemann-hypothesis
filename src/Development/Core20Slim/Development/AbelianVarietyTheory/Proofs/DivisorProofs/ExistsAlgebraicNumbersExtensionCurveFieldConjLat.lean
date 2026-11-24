module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbLLMem
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairIntAt
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.HighestWeightBelow
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TaylorCoeffConjugateSeriesStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaNormBoundHypothesesSatisfiedStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeUnitNormSqNonneg
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralJAndAlgebraicData
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaVacuaConjugatesCmPoints
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockVacEqJets
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTwoTorsionCMPointAllConjugates
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIntegerMapEqHalfOneAddSqrt
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Classical
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Nat.Basic
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.Hom.Rat
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.Algebra.CharP.IntermediateField
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.NatCast
public import Mathlib.Algebra.Order.ZeroLEOne
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Rat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Insert
public import Mathlib.Data.Set.Operations
public import Mathlib.FieldTheory.AlgebraicClosure
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.Normal.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.RingTheory.AlgebraTower
public import Mathlib.RingTheory.Algebraic.Basic
public import Mathlib.RingTheory.Algebraic.Defs
public import Mathlib.RingTheory.Ideal.Defs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.SumSize GlobalTheory.KerConjMean

namespace GlobalTheory.ConjExtend

theorem exists_extension_of_le (M : IntermediateField ℚ ℂ) (hle : M ≤ Qbar) (ρ : M →ₐ[ℚ] ℂ) :
    ∃ ρ' : Qbar →ₐ[ℚ] ℂ, ∀ x ∈ M, ρ' (TaylorLogMetric.liftM Qbar x) = ρ (TaylorLogMetric.liftM M x) := by
  let _ : Algebra M Qbar := (IntermediateField.inclusion hle).toRingHom.toAlgebra
  have : IsScalarTower ℚ M Qbar := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  have : Algebra.IsAlgebraic ℚ Qbar := algebraicClosure.isAlgebraic ℚ ℂ
  have : Algebra.IsAlgebraic M Qbar := Algebra.IsAlgebraic.tower_top (K := ℚ) M
  obtain ⟨φ, hφ⟩ := IsAlgClosed.surjective_domRestrict_of_isAlgebraic (K := ℚ) (L := M) (M := ℂ)
    (E := Qbar) ρ
  refine ⟨φ, fun x hx => ?_⟩
  rw [← hφ]
  unfold TaylorLogMetric.liftM
  rw [dite_eq_left hx, dite_eq_left (hle hx)]
  rfl

theorem fld_le (D : D7) (hI : GlobalTheory.NormSum.Inp D) (δ t0 : ℂ) (hc : Crv D D.host.ccK δ)
    (ht : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D D.host.ccK δ) t0) : GlobalTheory.KerConjMean.fld D δ t0 ≤ Qbar := by
  obtain ⟨hdata, htor⟩ := (GlobalTheory.CurveAlgebraic.integral_j_and_algebraic_data D hI.g1).2 _ δ hc
  have hwp : wpF (lamOf D D.host.ccK δ) t0 ∈ Qbar := by
    refine (htor t0 ⟨2, two_pos, by exact_mod_cast ht.1⟩ fun h0 => ?_).1
    obtain ⟨a, ha⟩ := GlobalTheory.NormSum.exists_integer_map_eq_w0 D
    have h1 := GlobalTheory.ArchNorm.mul_mem_lamOf D _ δ a h0
    rw [ha, mul_comm] at h1
    exact ht.2.1 h1
  unfold GlobalTheory.KerConjMean.fld
  rw [IntermediateField.adjoin_le_iff]
  rintro y (⟨x, rfl⟩ | rfl | rfl | rfl)
  · exact mem_algebraicClosure_iff.2
      ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).algHom D.what₂.embLL.toRatAlgHom)
  · exact hdata.2.1
  · exact hdata.2.2
  · exact hwp

theorem exists_extension_conj : ∀ (D : D7), GlobalTheory.NormSum.Inp D → ∀ (δ t0 : ℂ), Crv D D.host.ccK δ → GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D D.host.ccK δ) t0 →
    ∀ (σ : D.what₂.LL →+* ℂ), ∀ ρ ∈ GlobalTheory.KerConjMean.ext D δ t0 σ, ∃ ρ' : Qbar →ₐ[ℚ] ℂ,
      (∀ x, Formalism.MainNotions.StandardLatticesGL3.cj Qbar ρ' (D.what₂.embLL x) = σ x) ∧
      lamConj Qbar ρ' (lamOf D D.host.ccK δ) = lamConj (GlobalTheory.KerConjMean.fld D δ t0) ρ (GlobalTheory.KerConjMean.lat D δ) := by
  intro D hI δ t0 hc ht σ ρ hρ
  obtain ⟨ρ', h⟩ := exists_extension_of_le _ (fld_le D hI δ t0 hc ht) ρ
  refine ⟨ρ', fun x => ?_, ?_⟩
  · unfold Formalism.MainNotions.StandardLatticesGL3.cj
    rw [h _ (GlobalTheory.KerConjMean.embLL_mem D δ t0 x), ← hρ x]
    unfold TaylorLogMetric.liftM
    rw [dite_eq_left (GlobalTheory.KerConjMean.embLL_mem D δ t0 x)]
  · have h2 : g2 (lamOf D D.host.ccK δ) ∈ GlobalTheory.KerConjMean.fld D δ t0 :=
      IntermediateField.subset_adjoin ℚ _ (Or.inr (by simp))
    have h3 : g3 (lamOf D D.host.ccK δ) ∈ GlobalTheory.KerConjMean.fld D δ t0 :=
      IntermediateField.subset_adjoin ℚ _ (Or.inr (by simp))
    unfold lamConj
    rw [h _ h2, h _ h3]

end GlobalTheory.ConjExtend
