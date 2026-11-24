module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHalfIdem
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Hilbert90IntegralIdelesOfMovedPrimes
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmFiniteAdeleIntegralSeparatedComplete
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUnitaryExtension
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPeriodPairIdealCurveLattice
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutes
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FoundationProofs.DefiniteThetaPairTermsNormsIndependentRepresenta
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryDoubleCosetClassesFiniteCardLe
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryRationalConjIntersectionCardDvdInvariant
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaSpaceSelfDualPairAtMostLineStatement
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.ZeroLEOne
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.GroupTheory.Finiteness
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

namespace GlobalTheory.NormSum.Model

theorem vac_mem_TT {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (hc : Crv D cc δ) {a d : ℕ} {e0 : VC D a d → ℂ}
    (he : e0 ∈ Th D (tor0 D cc δ) (stdL D a) (stdL D d)) : e0 ∈ TT D (tor0 D cc δ) a d := by
  obtain ⟨-, hW, -⟩ := GlobalTheory.T.theta_space_selfDual_pair_at_most_line D (GlobalTheory.InducedType.induced_type D).1 cc δ hc a d (La0 D (tor0 D cc δ) a d)
    (Or.inr ⟨_, _, RepInv.sd_std D _, RepInv.sd_std D _, rfl⟩)
  refine ⟨he.1, 1, one_pos, fun x hx => ?_⟩
  rw [one_smul, hW x hx]
  funext w
  exact he.2 x hx w

end GlobalTheory.NormSum.Model
