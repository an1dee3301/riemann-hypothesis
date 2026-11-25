module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.LatticeFrames.StabOrd
public import Development.Core20Slim.Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.ContinuousSplitInv
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.LatticeFrames.EvalAtOneExtremalMul
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.AtTauExUniqueHolds
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.ContinuousTensMap
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.InfFam
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Finsupp.SMul
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.InvariantBasisNumber
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.KJInf Formalism.L2.Forms GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw.KUni

variable {D : D7} {V : HSp D}

theorem inv_eq {G B : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hB : Bᴴ * G * B = 1) : B⁻¹ = Bᴴ * G :=
  Matrix.inv_eq_left_inv hB

theorem mul_inv' {G B : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hB : Bᴴ * G * B = 1) : B * B⁻¹ = 1 := by
  rw [inv_eq hB]; exact mul_eq_one_comm.mp hB

theorem inv_mul' {G B : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hB : Bᴴ * G * B = 1) : B⁻¹ * B = 1 := by
  rw [inv_eq hB]; exact hB

theorem gB {G B : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hB : Bᴴ * G * B = 1) : Gᴴ * B * Bᴴ = 1 := by
  have h := congrArg Matrix.conjTranspose hB
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_one] at h
  exact mul_eq_one_comm.mp h

theorem conj_unitary {G B g : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hB : Bᴴ * G * B = 1) (hg : gᴴ * G * g = G) :
    B⁻¹ * g * B ∈ Matrix.unitaryGroup (Fin V.rank) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, inv_eq hB]
  have e : (Bᴴ * G * g * B)ᴴ * (Bᴴ * G * g * B) = Bᴴ * gᴴ * (Gᴴ * B * Bᴴ) * G * g * B := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  rw [e, gB hB, Matrix.mul_one]
  calc Bᴴ * gᴴ * G * g * B = Bᴴ * (gᴴ * G * g) * B := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hg, hB]

theorem back_unitary {G B u : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hB : Bᴴ * G * B = 1)
    (hu : u ∈ Matrix.unitaryGroup (Fin V.rank) ℂ) : (B * u * B⁻¹)ᴴ * G * (B * u * B⁻¹) = G := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at hu
  rw [inv_eq hB]
  have e : (B * u * (Bᴴ * G))ᴴ * G * (B * u * (Bᴴ * G)) = Gᴴ * B * uᴴ * (Bᴴ * G * B) * u * Bᴴ * G := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  rw [e, hB, Matrix.mul_one]
  calc Gᴴ * B * uᴴ * u * Bᴴ * G = Gᴴ * B * (uᴴ * u) * Bᴴ * G := by simp only [Matrix.mul_assoc]
    _ = (Gᴴ * B * Bᴴ) * G := by rw [hu, Matrix.mul_one]
    _ = G := by rw [gB hB, Matrix.one_mul]


open Formalism.IndefR.Eqv in
theorem psiT_continuous (τ : D.what₂.Tau) : Continuous (psiT D τ) := by
  have hsum : ∀ x : AE D, psiT D τ x = ∑ c, psiT D τ (algebraMap (AF D.host.F) (AE D) ((basAF D).repr x c)) *
      psiT D τ (basAF D c) := by
    intro x
    conv_lhs => rw [← (basAF D).sum_repr x]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Algebra.smul_def, map_mul]
  have hc : ∀ c, Continuous fun x : AE D => (basAF D).repr x c := fun c =>
    (continuous_apply c).comp (G5.tensCoordH (basE D) (AF D.host.F)).continuous
  have halg : Continuous fun a : AF D.host.F => psiT D τ (algebraMap (AF D.host.F) (AE D) a) := by
    have e : (fun a : AF D.host.F => psiT D τ (algebraMap (AF D.host.F) (AE D) a)) =
        fun a => thetaC D τ ((fstA D.host.F a) ⊗ₜ[D.host.F] (1 : D.host.E)) := by
      funext a
      simp only [psiT, RingHom.comp_apply, Algebra.TensorProduct.algebraMap_apply, infPart,
        AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul, map_one]
      rfl
    rw [e]
    exact ((isInfFam_thetaC D) τ).2.comp continuous_fst
  have hfun : (⇑(psiT D τ) : AE D → ℂ) = fun x => ∑ c, psiT D τ (algebraMap (AF D.host.F) (AE D)
      ((basAF D).repr x c)) * psiT D τ (basAF D c) := funext hsum
  rw [hfun]
  exact continuous_finsetSum _ fun c _ => (halg.comp (hc c)).mul continuous_const

open Formalism.IndefR.Eqv in
theorem inB_eq (V : HSp D) (B : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (g : GA D V) (τ : D.what₂.Tau) :
    inB (thetaC D) V B g τ = (B τ)⁻¹ * infMat D.sp.cm.sig V.gram (thetaC D τ) g * B τ := by
  rw [infMat_thetaC]; rfl

end GlobalTheory.SeeSaw.KUni


open GlobalTheory.SeeSaw.KUni Formalism.IndefR.Eqv in
theorem GlobalTheory.SeeSaw.ontoUni_inB : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (B : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ),
    IsInfFam θ → (∀ τ, (B τ)ᴴ * gramAt D V τ * B τ = 1) → OntoUni fun k : GinfC V => inB θ V B k.1 := by
  intro D θ V B hθ hB
  obtain rfl := eq_thetaC D hθ
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine continuous_pi fun τ => ?_
    have hm : Continuous fun g : GA D V => mt V g := Units.continuous_val.comp continuous_subtype_val
    have h1 : Continuous fun k : GinfC V => (mt V k.1).map (psiT D τ) :=
      (hm.comp continuous_subtype_val).matrix_map (psiT_continuous τ)
    exact (continuous_const.matrix_mul h1).matrix_mul continuous_const
  · intro k k' τ
    rw [inB_eq, inB_eq, inB_eq]
    simp only [Subgroup.coe_mul, infMat_thetaC, matA_mul, Matrix.map_mul]
    calc (B τ)⁻¹ * ((matA D V k).map (psiT D τ) * (matA D V k').map (psiT D τ)) * B τ
        = (B τ)⁻¹ * (matA D V k).map (psiT D τ) * (B τ * (B τ)⁻¹) * (matA D V k').map (psiT D τ) * B τ := by
          rw [mul_inv' (hB τ)]; simp only [Matrix.mul_assoc, Matrix.one_mul]
      _ = _ := by simp only [Matrix.mul_assoc]
  · intro k τ
    rw [inB_eq]
    exact conj_unitary (hB τ) (infMat_unitary' D V k.1 τ)
  · intro u hu
    have hgs : IsUnitFam D V fun τ => B τ * u τ * (B τ)⁻¹ := fun τ => back_unitary (hB τ) (hu τ)
    refine ⟨⟨famH D V _ hgs, famH_mem_GinfC D V _ hgs⟩, ?_⟩
    funext τ
    rw [inB_eq, infMat_famH]
    calc (B τ)⁻¹ * (B τ * u τ * (B τ)⁻¹) * B τ = ((B τ)⁻¹ * B τ) * u τ * ((B τ)⁻¹ * B τ) := by
          simp only [Matrix.mul_assoc]
      _ = u τ := by rw [inv_mul' (hB τ), Matrix.one_mul, Matrix.mul_one]
