module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BlockMatrixMul
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockMatrixTwoByTwoFinTranspose
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ModerateGrowthSchwartz
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelParabolicUnnMatrixBlockUpperTriangular
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
public import Development.Core20Slim.Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.HeisSch
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Basic
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.CharZero
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Basic
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.OuterMeasure.AE
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Filter.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Trace.Defs
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.LinearCombination.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Order
public import Mathlib.Topology.Separation.Hausdorff

@[expose] public section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.CompanionTheory.EisCovar
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.EisCovar.Weyl

variable {D : D7} {n : ℕ}

theorem mat_inv_eq (g : G D n) (hg : mat g = blk4 0 1 (-1) 0) : mat g⁻¹ = blk4 0 (-1) 1 0 := by
  have h : blk4 (0 : Mx D n n) (-1) 1 0 * mat g = 1 := by
    rw [hg, submatrix_fromBlocks_mul]
    simpa using block_matrix_one (n := n) (R := AE D)
  calc mat g⁻¹ = (blk4 (0 : Mx D n n) (-1) 1 0 * mat g) * mat g⁻¹ := by rw [h, Matrix.one_mul]
    _ = blk4 0 (-1) 1 0 := by rw [Matrix.mul_assoc, mat_mul_inv', Matrix.mul_one]

theorem inner_add_left (V : HSp D) (a b c : Mx D V.rank n) :
    inner V (a + b) c = inner V a c + inner V b c := by
  simp only [GlobalTheory.StdUnn.inner, adj_add, Matrix.add_mul]

theorem inner_add_right (V : HSp D) (a b c : Mx D V.rank n) :
    inner V a (b + c) = inner V a b + inner V a c := by
  simp only [GlobalTheory.StdUnn.inner, Matrix.mul_add]

theorem inner_neg_left (V : HSp D) (a c : Mx D V.rank n) : inner V (-a) c = -inner V a c := by
  simp only [GlobalTheory.StdUnn.inner, adj_neg, Matrix.neg_mul]

theorem inner_neg_right (V : HSp D) (a c : Mx D V.rank n) : inner V a (-c) = -inner V a c := by
  simp only [GlobalTheory.StdUnn.inner, Matrix.mul_neg]

theorem trA_add (a b : AE D) : trA (a + b) = trA a + trA b := map_add _ a b

theorem trA_neg (a : AE D) : trA (-a) = -trA a := map_neg _ a

theorem halfTr_add_swap (V : HSp D) (a b : Mx D V.rank n) :
    halfTr (Matrix.trace (inner V a b)) + halfTr (Matrix.trace (inner V b a)) =
      trA (Matrix.trace (inner V a b)) := by
  have h : algebraMap D.host.F (AF D.host.F) (1 / 2) + algebraMap D.host.F (AF D.host.F) (1 / 2) = 1 := by
    rw [← map_add (f := _), add_halves, map_one]
  rw [halfTr, halfTr, ← GlobalTheory.SWLink.trA_inner_comm V a b, ← add_mul, h, one_mul]

theorem phase (V : HSp D) (t x y z : Mx D V.rank n) :
    (trA (Matrix.trace (inner V (t + -x) y)) + halfTr (Matrix.trace (inner V x y))) +
        trA (Matrix.trace (inner V z (t + -x))) =
      (trA (Matrix.trace (inner V z (-x))) + halfTr (Matrix.trace (inner V y (-x)))) +
        trA (Matrix.trace (inner V (z + y) t)) := by
  have h := halfTr_add_swap V x y
  have c := GlobalTheory.SWLink.trA_inner_comm V t y
  have hn : halfTr (Matrix.trace (inner V y (-x))) = -halfTr (Matrix.trace (inner V y x)) := by
    rw [inner_neg_right, Matrix.trace_neg, halfTr, halfTr, trA_neg, mul_neg]
  rw [hn]
  simp only [inner_add_left, inner_add_right, inner_neg_left, inner_neg_right, Matrix.trace_add, Matrix.trace_neg,
    trA_add, trA_neg]
  rw [c, ← h]
  abel

end GlobalTheory.CompanionTheory.EisCovar.Weyl

namespace GlobalTheory.CompanionTheory.EisCovar

theorem covAt_weyl : ∀ (D : D7) (n : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (χ : (AE D)ˣ →* Circle) (θ : InfFam D) (μ : Measure (Mx D V.rank n)) (ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)), IsWeilSch ψ χ θ V μ ω → μ.IsAddHaarMeasure → ∀ g : G D n, mat g = blk4 0 1 (-1) 0 → CovAt ψ V ω g := by
  intro D n V ψ χ θ μ ω hω hμ g hg v Φ Ψ hΨ
  obtain ⟨i1, i2, i3, i4, -⟩ := lattice_Mx D V.rank n
  haveI : BorelSpace (Mx D V.rank n) := ⟨rfl⟩
  have hx : xPart (HMul.hMul v (mat g⁻¹) : Mx D V.rank (n + n)) = yPart v := by
    rw [Weyl.mat_inv_eq g hg, x_part_mul_block]; simp
  have hy : yPart (HMul.hMul v (mat g⁻¹) : Mx D V.rank (n + n)) = -xPart v := by
    rw [Weyl.mat_inv_eq g hg, y_part_mul_block]; simp
  funext z
  rw [hω.weyl g hg Ψ z]
  simp only [PositivityTheory.GramSchwartzFunctions.EC.Heisenberg₂]
  rw [hx, hy, hω.weyl g hg Φ (z + yPart v), ← integral_const_mul,
    ← integral_add_right_eq_self (μ := μ) (fun t => Ψ.1 t * ψ (trA (Matrix.trace (inner V z t)))) (-xPart v)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  have e := Weyl.phase V t (xPart v) (yPart v) z
  have e2 := congrArg ψ e
  rw [AddChar.map_add_eq_mul, AddChar.map_add_eq_mul ψ (_ + _)] at e2
  simp only [hΨ, PositivityTheory.GramSchwartzFunctions.EC.Heisenberg₂, neg_add_cancel_right]
  linear_combination (Φ.1 t) * e2

end GlobalTheory.CompanionTheory.EisCovar
