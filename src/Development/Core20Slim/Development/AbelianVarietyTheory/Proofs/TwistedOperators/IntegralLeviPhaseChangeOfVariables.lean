module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.PhaseApply
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.AddHaarLeftRightMulAdelicMatricesModuleStatement
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
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
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.ENNReal.Operations
public import Mathlib.Basic.ENNReal.Real
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.MeasurableSpace.Embedding
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Module
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Trace.Defs
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LeviNorm

variable {D : D7}

def sandwichHomeo {m n : ℕ} (P : GL (Fin m) (AE D)) (Q : GL (Fin n) (AE D)) : Mx D m n ≃ₜ Mx D m n where
  toFun u := HMul.hMul (HMul.hMul P.val u) Q.val
  invFun v := HMul.hMul (HMul.hMul (P⁻¹).val v) (Q⁻¹).val
  left_inv u := by
    simp only [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
    rw [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
  right_inv v := by
    simp only [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
    rw [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
  continuous_toFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  continuous_invFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const

theorem phase_sandwich (ψ : AddChar (AF D.host.F) ℂ) (W : HSp D) {r : ℕ} (h : GA D W) (a : GL (Fin r) (AE D))
    (y u : Mx D W.rank r) :
    phase ψ W (HMul.hMul (HMul.hMul (Formalism.L2.Theta.mt W h⁻¹) y) (GlobalTheory.MixModel.adj (a⁻¹).val))
      (HMul.hMul (HMul.hMul (Formalism.L2.Theta.mt W h⁻¹) u) a.val) = phase ψ W y u := by
  rw [phase_apply, phase_apply]
  congr 3
  have hu := GlobalTheory.MixModel.mt_unitary W h⁻¹
  have adj_mul_local {l m n : ℕ} (x : Mx D l m) (y : Mx D m n) :
      GlobalTheory.MixModel.adj (x * y) = GlobalTheory.MixModel.adj y * GlobalTheory.MixModel.adj x := by
    unfold GlobalTheory.MixModel.adj
    rw [Matrix.map_mul, Matrix.transpose_mul]
  change (GlobalTheory.MixModel.adj ((Formalism.L2.Theta.mt W h⁻¹) * y * (GlobalTheory.MixModel.adj (a⁻¹).val)) *
    (GlobalTheory.MixModel.gA W * ((Formalism.L2.Theta.mt W h⁻¹) * u * a.val))).trace = _
  simp only [adj_mul_local, GlobalTheory.MixModel.adj_adj]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (GlobalTheory.MixModel.gA W) (Formalism.L2.Theta.mt W h⁻¹),
    ← Matrix.mul_assoc (GlobalTheory.MixModel.adj (Formalism.L2.Theta.mt W h⁻¹)), hu, Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]

theorem absE_det_matHom_inv {W : HSp D} (h : GA D W)
    (hh : GlobalTheory.Doubling.absE D.host.F D.host.E (Matrix.GeneralLinearGroup.det (Formalism.L2.Theta.matHom W h)) = 1) :
    GlobalTheory.Doubling.absE D.host.F D.host.E (Matrix.GeneralLinearGroup.det (Formalism.L2.Theta.matHom W h⁻¹)) = 1 := by
  rw [map_inv, map_inv, map_inv, hh, inv_one]

theorem absE_det_pow_ne {r : ℕ} (a : GL (Fin r) (AE D)) (k : ℕ) :
    ((GlobalTheory.Doubling.absE D.host.F D.host.E (Matrix.GeneralLinearGroup.det a) : ENNReal) ^ k) ≠ 0 ∧
      ((GlobalTheory.Doubling.absE D.host.F D.host.E (Matrix.GeneralLinearGroup.det a) : ENNReal) ^ k) ≠ ⊤ :=
  ⟨pow_ne_zero _ (ENNReal.coe_ne_zero.2 ((Group.isUnit (Matrix.GeneralLinearGroup.det a)).map
    (GlobalTheory.Doubling.absE D.host.F D.host.E)).ne_zero), ENNReal.pow_ne_top ENNReal.coe_ne_top⟩


set_option maxHeartbeats 800000 in
theorem integral_phase_sandwich : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (W : HSp D) (r : ℕ) (μ : Measure (Mx D W.rank r)), μ.IsAddHaarMeasure → ∀ (h : GA D W), GlobalTheory.Doubling.absE D.host.F D.host.E (Matrix.GeneralLinearGroup.det (matHom W h)) = 1 → ∀ (a : GL (Fin r) (AE D)) (N : Mx D W.rank r → ℂ), Continuous N → Integrable N μ → Integrable (fun u : Mx D W.rank r => N (HMul.hMul (HMul.hMul (Formalism.L2.Theta.mt W h⁻¹) u) a.val)) μ ∧ ∀ y : Mx D W.rank r, ∫ u, GlobalTheory.LeviNorm.phase ψ W (HMul.hMul (HMul.hMul (Formalism.L2.Theta.mt W h⁻¹) y) (GlobalTheory.MixModel.adj (a⁻¹).val)) u * N u ∂μ = ((GlobalTheory.Doubling.absE D.host.F D.host.E (Matrix.GeneralLinearGroup.det a) : ℝ) : ℂ) ^ W.rank * ∫ u, GlobalTheory.LeviNorm.phase ψ W y u * N (HMul.hMul (HMul.hMul (Formalism.L2.Theta.mt W h⁻¹) u) a.val) ∂μ := by
  intro D ψ _ W r μ hμ h hh a N _ hNi
  haveI : BorelSpace (Mx D W.rank r) := ⟨rfl⟩
  have hmod := GlobalTheory.T.addHaar_leftRightMul_adelicMatrices_module D W.rank r μ hμ (Formalism.L2.Theta.matHom W h⁻¹) a
  have h1 := absE_det_matHom_inv h hh
  rw [h1, ENNReal.coe_one, one_pow, one_mul] at hmod
  obtain ⟨hc0, hcT⟩ := absE_det_pow_ne a W.rank
  let e := (sandwichHomeo (Formalism.L2.Theta.matHom W h⁻¹) a).toMeasurableEquiv
  have he : ∀ u, e u = HMul.hMul (HMul.hMul (Formalism.L2.Theta.mt W h⁻¹) u) a.val := fun _ => rfl
  have hmap : (Measure.map (fun u : Mx D W.rank r =>
      (HMul.hMul (HMul.hMul (Formalism.L2.Theta.matHom W h⁻¹).val (u : Matrix (Fin W.rank) (Fin r) (AE D))) a.val :
        Mx D W.rank r)) μ) = Measure.map e μ := rfl
  rw [hmap] at hmod
  refine ⟨?_, fun y => ?_⟩
  · rw [hmod, integrable_smul_measure hc0 hcT, integrable_map_equiv] at hNi
    exact hNi
  · conv_lhs => rw [hmod]
    rw [integral_smul_measure, integral_map_equiv]
    simp only [he, phase_sandwich]
    rw [ENNReal.toReal_pow, ENNReal.coe_toReal, Complex.real_smul]
    push_cast
    rfl

end GlobalTheory.LeviNorm
