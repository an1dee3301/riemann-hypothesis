module

public import Mathlib
public import Formalism.LocalRingCardinality.DataKerI
public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
public import Formalism.LocalToGlobal.KernelLattices.LateralTheory
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsNormSubEqOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutes
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Coeff
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Instances
public import Mathlib.Analysis.Normed.Group.Completion
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Logic.Basic
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Cast.Lemmas
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Mathlib.Topology.Algebra.GroupCompletion
public import Mathlib.Topology.Algebra.UniformField
public import Mathlib.Topology.Algebra.Valued.ValuationTopology
public import Mathlib.Topology.Algebra.Valued.ValuedField

@[expose] public section

open NumberField Filter Topology

noncomputable section

namespace GlobalTheory.Proof.IdempotentLatticeSequence

theorem norm_int_le {p : ℕ} [Fact p.Prime] {M : Type} [Field M] (φ : M →+* ℂ_[p]) (a : 𝓞 M) : ‖φ (a : M)‖ ≤ 1 := by
  obtain ⟨P, hmon, hev⟩ := RingOfIntegers.isIntegral_coe a
  have key : ∀ f : ℤ →+* ℂ_[p], Polynomial.eval₂ f (φ (a : M)) P = 0 := fun f => by
    rw [RingHom.ext_int f (φ.comp (algebraMap ℤ M)), ← Polynomial.hom_eval₂, hev, map_zero]
  exact GlobalTheory.SplitEmbSep.norm_le_one_of_isIntegral ⟨P, hmon, key _⟩







end GlobalTheory.Proof.IdempotentLatticeSequence
