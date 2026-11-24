module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FoundationProofs.ConjugateLatticeMeansPosLogAreaThetaBounded
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.PairingDivisors.StatementH
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.CharP.IntermediateField
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Rat
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.PosLog
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.FieldTheory.Minpoly.Field
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal

@[expose] public section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugate_lattice_means_posLog_area_theta_bounded : ∃ C : ℝ, 0 < C ∧ ∀ (D : D7), ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (t0 : ℂ), Crv D cc δ → GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 → ∀ L : ℝ, 1 ≤ L → Real.log D.host.rdE ≤ L → |logDerivativeAtOne D| ≤ L → ∀ (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M], g2 (lamOf D cc δ) ∈ M → g3 (lamOf D cc δ) ∈ M → wpF (lamOf D cc δ) t0 ∈ M → ∀ t : (M →ₐ[ℚ] ℂ) → ℂ, (∀ ρ, GL3Theta.IsTwoTorsionPointUnkilled D (lamConj M ρ (lamOf D cc δ)) (t ρ)) → (∑ ρ : M →ₐ[ℚ] ℂ, Real.posLog (area (lamConj M ρ (lamOf D cc δ)))⁻¹) / (Module.finrank ℚ M : ℝ) ≤ C * L ∧ (∑ ρ : M →ₐ[ℚ] ℂ, Real.posLog (nrm1Sq (lamConj M ρ (lamOf D cc δ)) (GL3Theta.th0 (lamConj M ρ (lamOf D cc δ)) (t ρ)))) / (Module.finrank ℚ M : ℝ) ≤ C * L := by
  first | exact @GlobalTheory.ArchFree.means.means_le | exact GlobalTheory.ArchFree.means.means_le | (intros; apply GlobalTheory.ArchFree.means.means_le <;> assumption)
