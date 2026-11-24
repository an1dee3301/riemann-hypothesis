module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.PairingDivisors.StatementH
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableSqTh
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FoundationProofs.TorsionPointPadicAbscissaNormLeOne
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Nat.Coprime
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Completion
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Logic.Basic
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.Topology.Algebra.Valued.ValuationTopology

@[expose] public section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.TorsionAbscissa

theorem norm_xAt_le_of_mul : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : GL3Theta.G1 p), GL3Theta.At D cc δ g → ∀ (N : ℕ) (v : ℂ), 0 < N → Nat.Coprime N p → (N : ℂ) * v ∈ g.abelian₂ → v ∉ g.abelian₂ → ‖GlobalTheory.EvenTheta.xAt g v‖ ≤ 1 := by
  intro D p _ cc δ g hg N v hN hcop hNv hv
  exact norm_xAt_le D p cc δ g hg v ⟨hv, N, hN, hcop, hNv⟩

end GlobalTheory.TorsionAbscissa
