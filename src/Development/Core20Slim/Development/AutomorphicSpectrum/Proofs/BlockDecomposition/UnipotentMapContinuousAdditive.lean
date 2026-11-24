module

public import Mathlib
public import Development.Core20Slim.Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.CoefDataExists
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaDecompositionUnitary
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelParabolicUnnMatrixBlockUpperTriangular
public import Development.Core20Slim.Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinPolesStd
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinSimplePoleOfDoublingMethod
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.LatticeFrames.HalfData
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemDoublingSiegelParabolicIffChartMemSiegelUnn
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StandardUnitaryChartSiegelLeviDetEq
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousStandardUnitaryChartAndSymmStatement
public import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BlockMatrixTwoByTwoFinStandardSkewMap
public import Development.Core20Slim.Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.AdelicConjTransposeBlockMatrixTwoByTwoFin
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
public import Development.Core20Slim.Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.BigCellDefs
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SatakeDualWeyl.Statement
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Block
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Finite
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Maps.Basic

@[expose] public section

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.SiegelUnip

open GlobalTheory.StdUnn GlobalTheory.StdUnn.Model GlobalTheory.StdUnn.LeftInvSect PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

variable {D : D7} {n : ℕ}

theorem nb_add {nb : hermA D n → G D n} (h : IsNMap nb) (b c : hermA D n) : nb (b + c) = nb b * nb c := by
  apply mat_inj
  rw [mat_mul, h, h, h, submatrix_fromBlocks_mul]
  simp [add_comm]

theorem nb_zero {nb : hermA D n → G D n} (h : IsNMap nb) : nb 0 = 1 := by
  apply mat_inj
  rw [mat_one, h]
  exact block_matrix_one

theorem nb_neg {nb : hermA D n → G D n} (h : IsNMap nb) (b : hermA D n) : nb (-b) = (nb b)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← nb_add h, neg_add_cancel, nb_zero h])

theorem continuous_blk (f : hermA D n → Mx D n n) (hf : Continuous f) :
    Continuous fun b : hermA D n => (blk4 1 (f b) 0 1 : Mx D (n + n) (n + n)) := by
  unfold blk4
  exact (Continuous.matrix_fromBlocks continuous_const hf continuous_const continuous_const).matrix_submatrix _ _

theorem nb_continuous {nb : hermA D n → G D n} (h : IsNMap nb) : Continuous nb := by
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) _
  rw [(isEmbedding_matHom (AF D.host.F) D.sp.cm.sig (Jst D n)).continuous_iff]
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact (continuous_blk _ continuous_subtype_val).congr fun b => (h b).symm
  · refine (continuous_blk (fun b => -b.1) continuous_subtype_val.neg).congr fun b => ?_
    have e : (matHom (AF D.host.F) D.sp.cm.sig (Jst D n) (nb b))⁻¹ = matHom (AF D.host.F) D.sp.cm.sig (Jst D n) (nb (-b)) := by
      rw [nb_neg h, map_inv]
    simp only [Function.comp_apply]
    rw [e]
    exact (h (-b)).symm

theorem nb_rat {nb : hermA D n → G D n} (h : IsNMap nb) {γ : hermA D n} (hγ : γ ∈ ratHerm D n) : nb γ ∈ GF D n := by
  obtain ⟨x, hx⟩ := mem_ratMx.1 hγ
  have hadj : adj (rat x) = rat x := by rw [hx]; exact γ.2
  let u : GL (Fin (n + n)) D.host.E := ⟨blk4 1 x 0 1, blk4 1 (-x) 0 1, by simp [submatrix_fromBlocks_mul, block_matrix_one], by simp [submatrix_fromBlocks_mul, block_matrix_one]⟩
  have hm : rat u.1 = mat (nb γ) := by
    rw [h]
    change (blk4 1 x 0 1).map (incA D) = _
    rw [GlobalTheory.StdUnn.Frame.block_matrix_map, show γ.1 = rat x from hx.symm]
    congr 1
    · exact Matrix.map_one _ (map_zero (incA D)) (map_one (incA D))
    · exact Matrix.map_zero _ (map_zero (incA D))
    · exact Matrix.map_one _ (map_zero (incA D)) (map_one (incA D))
  refine ⟨u, ?_, Units.ext hm⟩
  have hu : adj (mat (nb γ)) * JR (AF D.host.F) (Jst D n) * mat (nb γ) = JR (AF D.host.F) (Jst D n) := (nb γ).2
  change Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) u.1 * Jst D n * u.1 = Jst D n
  apply rat_injective
  rw [rat_mul, rat_mul, cT_sig, rat_conjTranspose, hm]
  exact hu

theorem nb_facts : ∀ (D : D7) (n : ℕ) (nb : PositivityTheory.GramSchwartzFunctions.BC.hermA D n → GlobalTheory.StdUnn.G D n), PositivityTheory.PfSWUS.IsNMap nb →
    Continuous nb ∧ (∀ b c, nb (b + c) = nb b * nb c) ∧ ∀ γ ∈ PositivityTheory.GramSchwartzFunctions.BC.ratHerm D n, nb γ ∈ GlobalTheory.StdUnn.GF D n :=
  fun _ _ _ h => ⟨nb_continuous h, nb_add h, fun _ hγ => nb_rat h hγ⟩

end GlobalTheory.CompanionTheory.SiegelUnip
