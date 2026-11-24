module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationProportionalityRatioLeBottomPairs
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ExistsSmallSpherical
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.PairingDivisors.StatementH
public import Formalism.QuotientMetricDivisors.Statement
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Classical
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Nat.Lemmas
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.PropLemmas
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Instances
public import Mathlib.Analysis.Normed.Group.Completion
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Logic.Basic
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Sets
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Nat.PadicValNat
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Fin.Basic
public import Mathlib.Order.Monotone.Defs
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.Algebra.UniformField
public import Mathlib.Topology.Algebra.Valued.ValuationTopology
public import Mathlib.Topology.Algebra.Valued.ValuedField

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuation_proportionalityRatio_le_bottomPairs : ∀ (D : D7) (N : ℕ) (B : ℝ) (Q : ℕ) (S : Finset ℕ) (del_vp : ℕ → ℝ) (b : ℝ), GlobalTheory.NormSum.Inp D →
    GlobalTheory.NormSum.Exponents S del_vp b → GlobalTheory.NormSum.CoordInt D N B Q del_vp →
    ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (σ : K →+* ℂ) (w : Formalism.PairingDivisionLocalBalance.Pl K) (p : ℕ) [Fact p.Prime],
    (p : 𝓞 K) ∈ w.asIdeal → ∀ (δ t0 : ℂ) (Q₁ Q₂ : ℕ), padicValNat p Q₁ ≤ padicValNat p Q →
    padicValNat p Q₂ ≤ padicValNat p Q →
    ∀ (P₁ P₁' : Pair D ⊤ δ t0 Q₁) (P₂ P₂' : Pair D ⊤ δ t0 Q₂), P₁.Small N B → P₁'.Small N B → P₂.Small N B →
    P₂'.Small N B → ∀ (hd₁ : P₁'.d = P₁.d) (hd₂ : P₂'.d = P₂.d) (b₁ b₂ v : ℂ)
    (M₁ : Tup D P₁.a P₁.d P₁.n → Tup D P₁'.a P₁'.d P₁'.n → ℤ) (M₂ : Tup D P₂'.a P₂'.d P₂'.n → Tup D P₂.a P₂.d P₂.n → ℤ),
    (∀ (h : GA D P₁.d) T, starRingEnd ℂ (P₁.coord h T) = b₁ * ∑ T', (M₁ T T' : ℂ) * P₁'.coord (hd₁ ▸ h) T') →
    (∀ (h : GA D P₂.d) T', P₂'.coord (hd₂ ▸ h) T' * b₂ = ∑ T, (M₂ T' T : ℂ) * starRingEnd ℂ (P₂.coord h T)) →
    b₂ ≠ 0 → v ∈ Qbar → (∀ lam : Qbar →+* ℂ_[p], ‖lamC lam v‖ = 1) →
    ∀ (γ z z' : K), b₁ = σ γ * b₂ * v → σ z = (P₁.norm : ℂ) → σ z' = (P₂'.norm : ℂ) → z ≠ 0 → z' ≠ 0 →
    (vw w γ : ℝ) ≤ vw w z + vw w z' + 6 * Formalism.PairingDivisionLocalBalance.wt S del_vp w := by
  first | exact @GlobalTheory.NormSum.LemmaC.vw_le_of_bottom_pairs | exact GlobalTheory.NormSum.LemmaC.vw_le_of_bottom_pairs | (intros; apply GlobalTheory.NormSum.LemmaC.vw_le_of_bottom_pairs <;> assumption)
