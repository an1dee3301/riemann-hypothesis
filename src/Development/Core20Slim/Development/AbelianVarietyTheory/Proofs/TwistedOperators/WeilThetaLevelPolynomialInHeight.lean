module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaGrowthOfThetaSquareIntegrable
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsFinNormComparison
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.WordDerivatives
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HermitianOrthogonalExtensionData
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LintegralCompactLe
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Order.Lattice
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Cast.Order.Ring
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.Order.Basic
public import Mathlib.Order.Bounds.Defs
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Lattice
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.ContinuousOn
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Order.OrderClosed
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped Pointwise

noncomputable section

namespace GlobalTheory.LevelGrowth

theorem level_poly : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (hθ : IsInfFam θ) (ε : Bool) (M X : HSp D)
    (χ χ' : (AE D)ˣ →* Circle) (ω : WRep M X) (hω : IsWeil ψ ε M X χ χ' ω) (Φ : WO M X → ℂ) (hΦ : IsThetaFunO ψ (sgn ε M) X Φ)
    (C₁ : Set (GA D M)) (hC₁ : IsCompact C₁),
    ∃ K₀ : Set (WO M X), K₀ ∈ nhds (0 : WO M X) ∧ IsCompact K₀ ∧ ∃ (m : ℝ) (e : ℕ), ∀ y ∈ C₁, ∀ h : GA D X,
      ∃ n : ℕ, 0 < n ∧ (n : ℝ) ≤ m * (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ X h : ℝ) ^ e ∧
        ∀ u ∈ K₀, u.map (infPart D) = 0 → heisO ψ (sgn ε M) X (n • u) (ω (y, h) Φ) = ω (y, h) Φ := by
  intro D ψ θ hθ ε M X χ χ' ω hω Φ hΦ C₁ hC₁
  obtain ⟨U, hU, hΦU⟩ := GlobalTheory.Size.isTheta_iff_level.1 hΦ
  obtain ⟨K₀, h0, hK₀, m, hlev⟩ := GlobalTheory.KernelSeminorm.exists_level_multiple (S := sgn ε M) (T := X) hU
  obtain ⟨B, hB⟩ := hC₁.bddAbove_image
    ((GlobalTheory.Grow.continuous_height (sgn ε M)).comp (continuous_ofSgn_symm ε M)).continuousOn
  obtain ⟨C, hC, hcmp⟩ := GlobalTheory.Grow.height_comparison X hθ
  refine ⟨K₀, h0, hK₀, m * max B 0 * C, 1, fun y hy h => ?_⟩
  set g := (ofSgn ε M).symm y with hg
  obtain ⟨n, hn, hnle, hmem⟩ := hlev g h
  refine ⟨n, hn, ?_, fun u hu hinf => ?_⟩
  · have hgB : GlobalTheory.Grow.height (sgn ε M) g ≤ max B 0 := (hB ⟨y, hy, rfl⟩).trans (le_max_left _ _)
    have hhC : GlobalTheory.Grow.height X h ≤ C * (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ X h : ℝ) := (hcmp h).2
    have hm0 : (0 : ℝ) ≤ m := m.cast_nonneg
    have hg0 := (GlobalTheory.Grow.height_pos (sgn ε M) g).le
    have hh0 := (GlobalTheory.Grow.height_pos X h).le
    calc (n : ℝ) ≤ m * (GlobalTheory.Grow.height (sgn ε M) g * GlobalTheory.Grow.height X h) := hnle
      _ ≤ m * (max B 0 * (C * (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ X h : ℝ))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hgB hhC hh0 (le_max_right _ _)) hm0
      _ = m * max B 0 * C * (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ X h : ℝ) ^ 1 := by ring
  · have hv : (actO (sgn ε M) X g⁻¹ h⁻¹ (n • u)).map (infPart D) = 0 := by
      have : (n • u).map (infPart D) = 0 := by
        ext i j
        have h3 : infPart D (u i j) = 0 := congrFun (congrFun hinf i) j
        exact (map_nsmul (infPart D) n (u i j)).trans ((congrArg (n • ·) h3).trans (nsmul_zero n))
      unfold actO
      rw [Matrix.map_mul, Matrix.map_mul, this, Matrix.mul_zero, Matrix.zero_mul]
    have hfix := hΦU.2 _ (hmem u hu hinf) hv
    have e := hω.om_heis g h (actO (sgn ε M) X g⁻¹ h⁻¹ (n • u)) Φ hΦ
    rw [hfix, GlobalTheory.ThetaGrowth.actO_mul, mul_inv_cancel, mul_inv_cancel, GlobalTheory.ThetaGrowth.actO_one] at e
    have e2 : (WRep.toSgn ε ω) (g, h) = ω (y, h) := by
      simp [WRep.toSgn, hg]
    rw [e2] at e
    exact e.symm

end GlobalTheory.LevelGrowth
