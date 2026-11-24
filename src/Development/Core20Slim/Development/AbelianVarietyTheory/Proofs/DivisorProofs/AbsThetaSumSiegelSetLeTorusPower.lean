module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.LatticeFrames.RealSizeNonneg
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatAdelicMatrixContinuousLeMajorantStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSchwartzBruhatAdelicMatrixOfMemAdelicSchwartzStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelTorusTsumMajorantTranslatedRationalPointsLStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicMatrixSchwartzMajorantInvMulLeStatement
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ModerateGrowthSchwartz
public import Development.Core20Slim.Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SchwartzBruhatMixedFamilies
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
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Basic
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.ENNReal.Real
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.Topology.Algebra.InfiniteSum.SummationFilter
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Order.Real
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TorusBound

theorem absTheta_le_torus : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (n : ℕ) (r : ℕ) (X Y : Matrix (Fin V.rank) (Fin r) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∀ c : ℝ, 0 < c → ∀ Q : Set (GA D V), IsCompact Q → ∀ Φ : schwartzA θ V.rank n, ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ GlobalTheory.SiegelSet.cone r c, ∀ a : GA D V, GlobalTheory.SiegelSet.IsTorusElt D.sp.cm.sig V.gram X Y t a → ∀ y ∈ Q, GlobalTheory.SiegelFormula.absTheta V Φ.1 (a * y) ≤ ENNReal.ofReal (C * ∏ i, t i ^ (Module.finrank ℚ D.host.F * (2 * n))) := by
  intro D θ hθ V n r X Y hXY c hc Q hQ Φ
  have hSB := GlobalTheory.T.isSchwartzBruhatAdelicMatrix_of_mem_adelicSchwartz D θ hθ V.rank n Φ.1 Φ.2
  obtain ⟨-, K, hK, hmaj⟩ := GlobalTheory.T.schwartzBruhatAdelicMatrix_continuous_le_majorant D θ hθ V.rank n Φ.1 hSB
  obtain ⟨K', hK', hmul⟩ := GlobalTheory.T.adelicMatrixSchwartzMajorant_inv_mul_le D θ hθ V n Q hQ K hK
  obtain ⟨N, C₁, hC₁, hframe⟩ := GlobalTheory.T.siegelTorus_tsum_majorant_translatedRationalPoints_le D θ hθ V n r X Y hXY c hc K' hK'
  obtain ⟨C₀, hC₀⟩ := hmaj N
  obtain ⟨C₂, hC₂, hmul'⟩ := hmul N
  set A : ℝ := max C₀ 0 * C₂ with hA
  have hA0 : 0 ≤ A := mul_nonneg (le_max_right _ _) hC₂
  refine ⟨A * C₁, mul_nonneg hA0 hC₁, ?_⟩
  intro t ht a ha y hy
  have hpt : ∀ ξ : Matrix (Fin V.rank) (Fin n) D.host.E,
      GlobalTheory.SiegelFormula.invPt V (a * y) ξ
        = (HMul.hMul (Formalism.L2.Theta.mt V y⁻¹) (GlobalTheory.SiegelFormula.invPt V a ξ) : Mx D V.rank n) := by
    intro ξ
    have h2 : Formalism.L2.Theta.mt V (a * y)⁻¹ = Formalism.L2.Theta.mt V y⁻¹ * Formalism.L2.Theta.mt V a⁻¹ := by
      rw [mul_inv_rev]; rfl
    simp only [GlobalTheory.SiegelFormula.invPt, h2, Matrix.mul_assoc]
  have hterm : ∀ ξ : Matrix (Fin V.rank) (Fin n) D.host.E,
      ‖Φ.1 (GlobalTheory.SiegelFormula.invPt V (a * y) ξ)‖ₑ
        ≤ ENNReal.ofReal A * ENNReal.ofReal (GlobalTheory.Unf.maj θ K' N (GlobalTheory.SiegelFormula.invPt V a ξ)) := by
    intro ξ
    rw [← ENNReal.ofReal_mul hA0, ← ofReal_norm_eq_enorm]
    apply ENNReal.ofReal_le_ofReal
    rw [hpt ξ]
    set x := GlobalTheory.SiegelFormula.invPt V a ξ
    have h1 := hC₀ (HMul.hMul (Formalism.L2.Theta.mt V y⁻¹) x : Mx D V.rank n)
    have h2 := hmul' y hy x
    have hm0 := GlobalTheory.Unf.maj_nonneg θ K N (HMul.hMul (Formalism.L2.Theta.mt V y⁻¹) x : Mx D V.rank n)
    calc ‖Φ.1 (HMul.hMul (Formalism.L2.Theta.mt V y⁻¹) x : Mx D V.rank n)‖
        ≤ C₀ * GlobalTheory.Unf.maj θ K N (HMul.hMul (Formalism.L2.Theta.mt V y⁻¹) x : Mx D V.rank n) := h1
      _ ≤ max C₀ 0 * GlobalTheory.Unf.maj θ K N (HMul.hMul (Formalism.L2.Theta.mt V y⁻¹) x : Mx D V.rank n) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hm0
      _ ≤ max C₀ 0 * (C₂ * GlobalTheory.Unf.maj θ K' N x) :=
          mul_le_mul_of_nonneg_left h2 (le_max_right _ _)
      _ = A * GlobalTheory.Unf.maj θ K' N x := by rw [hA, mul_assoc]
  calc GlobalTheory.SiegelFormula.absTheta V Φ.1 (a * y)
      = ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, ‖Φ.1 (GlobalTheory.SiegelFormula.invPt V (a * y) ξ)‖ₑ := rfl
    _ ≤ ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E,
          ENNReal.ofReal A * ENNReal.ofReal (GlobalTheory.Unf.maj θ K' N (GlobalTheory.SiegelFormula.invPt V a ξ)) :=
        ENNReal.tsum_le_tsum hterm
    _ = ENNReal.ofReal A * ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E,
          ENNReal.ofReal (GlobalTheory.Unf.maj θ K' N (GlobalTheory.SiegelFormula.invPt V a ξ)) := ENNReal.tsum_mul_left
    _ ≤ ENNReal.ofReal A * ENNReal.ofReal (C₁ * ∏ i, t i ^ (Module.finrank ℚ D.host.F * (2 * n))) :=
        by gcongr; exact hframe t ht a ha
    _ = ENNReal.ofReal (A * C₁ * ∏ i, t i ^ (Module.finrank ℚ D.host.F * (2 * n))) := by
        rw [← ENNReal.ofReal_mul hA0]; congr 1; ring

end GlobalTheory.TorusBound
