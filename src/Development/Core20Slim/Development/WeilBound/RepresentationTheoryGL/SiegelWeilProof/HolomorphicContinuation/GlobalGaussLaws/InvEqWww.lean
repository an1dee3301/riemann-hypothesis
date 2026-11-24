module

public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.CompAtSubSIns
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HalfTrAddSwap
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.ContinuousBw
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.ContinuousInsT
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.ContinuousKer
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.PlaceFacts
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.SchDecay
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
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
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open Formalism.IndefR.Eqv (psiT eq_thetaC)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.FTH

open PositivityTheory.Rg.Sw.Glob.FTP PositivityTheory.Rg.Sw.Glob.PlaceFactsH
open Classical

variable {D : D7} {n m : ℕ}

theorem Aw_away {θ : InfFam D} (hθ : IsInfFam θ) {V : HSp D} {τ : D.what₂.Tau}
    {fr : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hdet : IsUnit fr.det) (ψ : AddChar (AF D.host.F) ℂ)
    (μ : Measure (Mx D V.rank n)) (Ψ : Mx D V.rank n → ℂ) (x x' : Mx D V.rank n)
    (hx : ∀ τ', τ' ≠ τ → compAt θ τ' x = compAt θ τ' x') (hf : x.map (finPart D) = x'.map (finPart D)) :
    Aw ψ V θ τ fr μ Ψ x = Aw ψ V θ τ fr μ Ψ x' := by
  have e : Bw ψ V θ τ fr Ψ x = Bw ψ V θ τ fr Ψ x' := by
    funext y
    unfold Bw
    rw [inner_away hθ x x' _ hx hf (compAt_sub_sIns hθ hdet y)]
  unfold Aw
  rw [e]

set_option maxHeartbeats 800000 in
theorem mat_ww (w : G D n) (hw : mat w = blk4 0 1 (-1) 0) : mat (w * w) = blk4 (-1) 0 0 (-1) := by
  rw [mat_mul', hw, submatrix_fromBlocks_mul]
  simp

set_option maxHeartbeats 800000 in
theorem inv_eq_www (w : G D n) (hw : mat w = blk4 0 1 (-1) 0) : w⁻¹ = w * w * w := by
  apply mat_inj
  rw [GlobalTheory.CompanionTheory.EisCovar.Weyl.mat_inv_eq w hw, mat_mul', mat_ww w hw, hw, submatrix_fromBlocks_mul]
  simp

end PositivityTheory.Rg.Sw.Glob.FTH
