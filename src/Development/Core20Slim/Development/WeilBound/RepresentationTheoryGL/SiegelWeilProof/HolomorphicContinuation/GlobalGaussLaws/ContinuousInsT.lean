module

public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.PsiEqOfFin
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.FibFact
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocCellT
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.AtTauExUniqueHolds
public import Development.Core20Slim.Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.ContinuousPsiT
public import Development.Core20Slim.Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.ContinuousSplitInv
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.InfFam
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Classical
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.StdUnn
open Formalism.IndefR.Eqv (psiT psiT_sigR psiT_inclR thetaC eq_thetaC glueA splitInv psiT_glueA finPart_glueA ae_ext'
  continuous_glueA continuous_splitInv continuous_psiT)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.FTP

open Classical

variable {D : D7} {m n : ℕ}

def insT (τ : D.what₂.Tau) (v : Matrix (Fin m) (Fin n) ℂ) : Mx D m n :=
  Matrix.of fun i j => glueA D (splitInv D fun τ' => if τ' = τ then v i j else 0) 0

theorem psiT_insT (τ τ' : D.what₂.Tau) (v : Matrix (Fin m) (Fin n) ℂ) (i : Fin m) (j : Fin n) :
    psiT D τ' (insT τ v i j) = if τ' = τ then v i j else 0 := psiT_glueA D τ' _ 0

theorem finPart_insT (τ : D.what₂.Tau) (v : Matrix (Fin m) (Fin n) ℂ) (i : Fin m) (j : Fin n) :
    finPart D (insT τ v i j) = 0 := finPart_glueA D _ 0

theorem insT_add (τ : D.what₂.Tau) (v w : Matrix (Fin m) (Fin n) ℂ) : insT (D := D) τ (v + w) = insT τ v + insT τ w := by
  ext i j
  apply ae_ext' D
  · intro τ'
    rw [Matrix.add_apply, RingHom.map_add (f := _), psiT_insT, psiT_insT, psiT_insT]
    split_ifs <;> simp
  · rw [Matrix.add_apply, RingHom.map_add (f := _), finPart_insT, finPart_insT, finPart_insT, add_zero]

theorem insT_zero (τ : D.what₂.Tau) : insT (D := D) (m := m) (n := n) τ 0 = 0 := by
  ext i j
  apply ae_ext' D
  · intro τ'
    rw [psiT_insT, Matrix.zero_apply, Matrix.zero_apply, RingHom.map_zero]
    split_ifs <;> rfl
  · rw [finPart_insT, Matrix.zero_apply, RingHom.map_zero]

theorem continuous_insT (τ : D.what₂.Tau) : Continuous (insT (D := D) (m := m) (n := n) τ) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  refine (continuous_glueA D 0).comp ((continuous_splitInv D).comp (continuous_pi fun τ' => ?_))
  split_ifs
  · exact (continuous_apply j).comp (continuous_apply i)
  · exact continuous_const

theorem compAt_insT {θ : InfFam D} (hθ : IsInfFam θ) (τ τ' : D.what₂.Tau) (v : Matrix (Fin m) (Fin n) ℂ) :
    compAt θ τ' (insT τ v) = if τ' = τ then v else 0 := by
  rw [eq_thetaC D hθ]
  ext i j
  show psiT D τ' (insT τ v i j) = _
  rw [psiT_insT]
  split_ifs <;> rfl

theorem finMap_insT (τ : D.what₂.Tau) (v : Matrix (Fin m) (Fin n) ℂ) : (insT (D := D) τ v).map (finPart D) = 0 := by
  ext i j; exact finPart_insT τ v i j

def sIns (τ : D.what₂.Tau) (fr : Matrix (Fin m) (Fin m) ℂ) : (Fin m → Fin n → ℂ) →+ Mx D m n where
  toFun u := insT τ (fr * Matrix.of u)
  map_zero' := by simp [insT_zero]
  map_add' u v := by
    rw [show Matrix.of (u + v) = Matrix.of u + Matrix.of v from rfl, Matrix.mul_add, insT_add]


set_option synthInstance.maxHeartbeats 400000 in
def piF (θ : InfFam D) (τ : D.what₂.Tau) (fr : Matrix (Fin m) (Fin m) ℂ) : Mx D m n →+ (Fin m → Fin n → ℂ) where
  toFun y := Matrix.of.symm (fr⁻¹ * compAt θ τ y)
  map_zero' := by
    ext i j
    simp [compAt]
  map_add' y y' := by
    have h : compAt θ τ (y + y') = compAt θ τ y + compAt θ τ y' := by
      ext i j; simp only [compAt, Matrix.map_apply, Matrix.add_apply, RingHom.map_add (f := _)]
    ext i j
    simp only [h, Matrix.mul_add]
    rfl

set_option synthInstance.maxHeartbeats 400000 in
theorem piF_sIns {θ : InfFam D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) {fr : Matrix (Fin m) (Fin m) ℂ}
    (hfr : IsUnit fr.det) (u : Fin m → Fin n → ℂ) : piF θ τ fr (sIns (D := D) τ fr u) = u := by
  show Matrix.of.symm (fr⁻¹ * compAt θ τ (insT τ (fr * Matrix.of u))) = u
  rw [compAt_insT hθ, if_pos rfl, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hfr, Matrix.one_mul]
  rfl

theorem continuous_piF {θ : InfFam D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) (fr : Matrix (Fin m) (Fin m) ℂ) :
    Continuous (piF (n := n) θ τ fr) := by
  have h : Continuous fun y : Mx D m n => (fr⁻¹ * compAt θ τ y : Matrix (Fin m) (Fin n) ℂ) := by
    refine Continuous.matrix_mul continuous_const ?_
    rw [eq_thetaC D hθ]
    exact Continuous.matrix_map continuous_id (Formalism.IndefR.Eqv.continuous_psiT (D := D) τ)
  exact h

theorem continuous_sIns (τ : D.what₂.Tau) (fr : Matrix (Fin m) (Fin m) ℂ) :
    Continuous (sIns (D := D) (n := n) τ fr) := by
  show Continuous fun u : Fin m → Fin n → ℂ => insT τ (fr * Matrix.of u)
  exact (continuous_insT τ).comp (Continuous.matrix_mul continuous_const continuous_id)

end PositivityTheory.Rg.Sw.Glob.FTP
