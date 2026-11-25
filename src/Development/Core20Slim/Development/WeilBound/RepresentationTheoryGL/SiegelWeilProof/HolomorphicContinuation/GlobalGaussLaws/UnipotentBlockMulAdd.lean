module

public import Mathlib
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.HermFourierZero
public import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OfHermEBijective
public import Development.Core20Slim.Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.CoefDataExists
public import Development.Core20Slim.Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.BigCellDefs
public import Development.Core20Slim.Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.ThetaOrbits
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.FourierZeroN
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Function
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
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
public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Block
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Group.Subgroup
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Maps.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Order
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

open GlobalTheory.CompanionTheory.HermPoisson

variable {D : D7} {n : ℕ}

namespace FZNH

theorem unipotent_block_mul_add {R : Type} [CommRing R] (b c : Matrix (Fin n) (Fin n) R) :
    blk4 1 b 0 1 * blk4 1 c 0 1 = blk4 (1 : Matrix (Fin n) (Fin n) R) (b + c) 0 1 := by
  unfold blk4
  rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  congr 1
  simp [add_comm]

theorem block_matrix_one {R : Type} [CommRing R] : blk4 (1 : Matrix (Fin n) (Fin n) R) 0 0 1 = 1 := by
  unfold blk4
  rw [Matrix.fromBlocks_one]
  exact Matrix.submatrix_one_equiv _

theorem mat_injective : Function.Injective (mat (D := D) (n := n)) := fun x y h =>
  GlobalTheory.AdelicU.matHom_injective _ _ _ (Units.ext h)

theorem mat_mul (x y : G D n) : mat (x * y) = mat x * mat y := by
  simp only [mat, map_mul, Units.val_mul]

theorem mat_one : mat (1 : G D n) = 1 := by
  simp only [mat, map_one, Units.val_one]

theorem nb_add {nb : hermA D n → G D n} (h : PositivityTheory.PfSWUS.IsNMap nb) (b c : hermA D n) :
    nb (b + c) = nb b * nb c := by
  apply mat_injective
  rw [mat_mul, h, h, h, unipotent_block_mul_add]
  rfl

theorem nb_zero {nb : hermA D n → G D n} (h : PositivityTheory.PfSWUS.IsNMap nb) : nb 0 = 1 := by
  apply mat_injective
  rw [h, mat_one]
  exact block_matrix_one

theorem nb_neg {nb : hermA D n → G D n} (h : PositivityTheory.PfSWUS.IsNMap nb) (b : hermA D n) : (nb b)⁻¹ = nb (-b) := by
  have h' : nb (-b) * nb b = 1 := by rw [← nb_add h, neg_add_cancel, nb_zero h]
  exact (eq_inv_of_mul_eq_one_left h').symm

set_option synthInstance.maxHeartbeats 400000 in
theorem nb_continuous {nb : hermA D n → G D n} (h : PositivityTheory.PfSWUS.IsNMap nb) : Continuous nb := by
  obtain ⟨i1, -⟩ := lattice_Mx D n n
  haveI : IsTopologicalAddGroup (Mx D n n) := i1
  have he := GlobalTheory.AdelicU.isEmbedding_matHom (AF D.host.F) D.sp.cm.sig (Jst D n)
  rw [he.continuous_iff, Units.continuous_iff]
  have hc : Continuous fun b : hermA D n => blk4 (1 : Mx D n n) b.1 0 1 := by
    unfold blk4
    exact (continuous_const.matrix_fromBlocks continuous_subtype_val continuous_const continuous_const).matrix_submatrix _ _
  refine ⟨?_, ?_⟩
  · convert hc using 1
    funext b
    exact h b
  · convert hc.comp continuous_neg using 1
    funext b
    simp only [Function.comp_apply]
    rw [← map_inv, nb_neg h]
    exact h (-b)

end FZNH

open FZNH

theorem fourierZeroN : FourierZeroN := by
  intro D n ψ hψ nb lam 𝓖 hcd f hf hinv hco
  obtain ⟨hnb, hH, h𝓖, -⟩ := hcd
  funext g
  have key := hermFourierZero D n ψ hψ lam hH 𝓖 h𝓖 (fun b => f (nb b * g))
    (hf.comp ((nb_continuous hnb).mul continuous_const)) (fun x l hl => by
      obtain ⟨β, hβ⟩ := (ofHermE_bijective (D := D) (r := n)).2 ⟨l, hl⟩
      show f (nb (x + l) * g) = f (nb x * g)
      rw [show x + l = l + x from add_comm x l, nb_add hnb, mul_assoc]
      refine hinv l ⟨β, ?_⟩ _
      rw [← ofHermE_val, hβ]) (fun β => hco β g) 0
  simpa [nb_zero hnb] using key

end PositivityTheory.Rg.Sw.Glob
