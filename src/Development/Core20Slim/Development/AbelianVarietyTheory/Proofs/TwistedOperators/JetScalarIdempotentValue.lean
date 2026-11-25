module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitOff
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalisedFamilyEqTensorPowerVacuum
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.JetScalarUnitModulus
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitIdempotentUnitDecomposition
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.JetScalarLocalIdentity
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Init.Classical
public import Init.Core
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.GroupWithZero.Units.Lemmas
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Degree.Operations
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Instances
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Completion
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Completion
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Logic.Basic
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Rat.Defs
public import Mathlib.FieldTheory.AlgebraicClosure
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.Order.Basic
public import Mathlib.RingTheory.Algebraic.Defs
public import Mathlib.Topology.Algebra.GroupCompletion
public import Mathlib.Topology.Algebra.UniformField
public import Mathlib.Topology.Algebra.UniformRing
public import Mathlib.Topology.Algebra.Valued.ValuationTopology
public import Mathlib.Topology.Algebra.Valued.ValuedField

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

noncomputable section

namespace GlobalTheory.SplitMoveKappa

theorem qbar_of_root {ζ : ℂ} {n : ℕ} (hn : 0 < n) (hζ : ζ ^ n = 1) : ζ ∈ TaylorLogMetric.Qbar := by
  have halg : IsAlgebraic ℚ ζ := by
    refine ⟨Polynomial.X ^ n - Polynomial.C 1, ?_, ?_⟩
    · exact Polynomial.X_pow_sub_C_ne_zero hn 1
    · simp [hζ]
  exact mem_algebraicClosure_iff.2 halg

theorem mod1All_root {ζ : ℂ} {n : ℕ} (hn : 0 < n) (hζ : ζ ^ n = 1) : Mod1All ζ := by
  refine ⟨qbar_of_root hn hζ, fun σ => ?_⟩
  have h1 : (⟨ζ, qbar_of_root hn hζ⟩ : TaylorLogMetric.Qbar) ^ n = 1 := by ext; simpa using hζ
  have h2 : (σ ⟨ζ, qbar_of_root hn hζ⟩) ^ n = 1 := by rw [← map_pow, h1, map_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 (by rw [← norm_pow, h2, norm_one])

theorem lamC_mem {q : ℕ} [Fact q.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[q]) {x : ℂ} (h : x ∈ TaylorLogMetric.Qbar) :
    TaylorLogMetric.lamC lam x = lam ⟨x, h⟩ := dif_pos h

theorem unitAt_mul {q : ℕ} [Fact q.Prime] {x y : ℂ} (hx : x ∈ TaylorLogMetric.Qbar) (hy : y ∈ TaylorLogMetric.Qbar)
    (ux : GlobalTheory.MovedKappaEx.UnitAt q x) (uy : GlobalTheory.MovedKappaEx.UnitAt q y) : GlobalTheory.MovedKappaEx.UnitAt q (x * y) := by
  intro lam
  have e : (⟨x * y, mul_mem hx hy⟩ : TaylorLogMetric.Qbar) = ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
  have hx' := ux lam
  have hy' := uy lam
  rw [lamC_mem lam hx] at hx'
  rw [lamC_mem lam hy] at hy'
  rw [lamC_mem lam (mul_mem hx hy), e, map_mul, norm_mul, hx', hy', one_mul]

theorem unitAt_inv {q : ℕ} [Fact q.Prime] {x : ℂ} (hx : x ∈ TaylorLogMetric.Qbar)
    (ux : GlobalTheory.MovedKappaEx.UnitAt q x) : GlobalTheory.MovedKappaEx.UnitAt q x⁻¹ := by
  intro lam
  have e : (⟨x⁻¹, inv_mem hx⟩ : TaylorLogMetric.Qbar) = (⟨x, hx⟩ : TaylorLogMetric.Qbar)⁻¹ := rfl
  have hx' := ux lam
  rw [lamC_mem lam hx] at hx'
  rw [lamC_mem lam (inv_mem hx), e, map_inv₀, norm_inv, hx', inv_one]

theorem unitAt_root (q : ℕ) [Fact q.Prime] {ζ : ℂ} {n : ℕ} (hn : 0 < n) (hζ : ζ ^ n = 1) :
    GlobalTheory.MovedKappaEx.UnitAt q ζ := by
  intro lam
  have h1 : (⟨ζ, qbar_of_root hn hζ⟩ : TaylorLogMetric.Qbar) ^ n = 1 := by ext; simpa using hζ
  have h2 : (lam ⟨ζ, qbar_of_root hn hζ⟩) ^ n = 1 := by rw [← map_pow, h1, map_one]
  rw [lamC_mem lam (qbar_of_root hn hζ)]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 (by rw [← norm_pow, h2, norm_one])

end GlobalTheory.SplitMoveKappa
