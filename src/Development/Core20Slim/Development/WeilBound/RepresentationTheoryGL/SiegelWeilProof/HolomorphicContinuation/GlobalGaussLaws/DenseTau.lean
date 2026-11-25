module

public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DenseA
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DenseC
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobData
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.FourierZeroN
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.IsSingTest
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.AtTauExUniqueHolds
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.InfFam
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Classical
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
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Tactic.Group
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Closure
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

open Matrix Topology
open scoped Matrix TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum
open GlobalTheory.StdUnn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

open Formalism.IndefR.Eqv (psiT thetaC)

theorem denseTau : DenseTau := by
  intro D n θ τ ι hθ hι y O hO hy
  obtain rfl := Formalism.IndefR.Eqv.eq_thetaC D hθ
  have hcl := DenseP.gam_dense (D := D) DenseP.genSt τ y
  obtain ⟨y', hy'O, γ, hγ, hγe⟩ := mem_closure_iff.1 hcl O hO hy
  have hc : ∀ τ' (w : Formalism.IndefR.Datum.Mx D (n + n) (n + n)), compAt (thetaC D) τ' w = w.map (psiT D τ') :=
    fun _ _ => rfl
  have hy' : (mat (ι y')).map (psiT D τ) = Glob.reidx (mR y') := (hc τ _).symm.trans (hι.2 y').1
  refine ⟨γ, hγ, y', hy'O, γ * (ι y')⁻¹, by group, fun y'' => ?_⟩
  have hR : (mat (γ * (ι y')⁻¹)).map (psiT D τ) = 1 := by
    have h1 : (mat γ).map (psiT D τ) = (mat (γ * (ι y')⁻¹)).map (psiT D τ) * (mat (ι y')).map (psiT D τ) := by
      rw [← Matrix.map_mul, ← DenseP.mat_mul, inv_mul_cancel_right]
    rw [hγe, hy'] at h1
    have h2 : Glob.reidx (mR y') * Glob.reidx (mR y'⁻¹) = 1 := by
      rw [← DenseP.reidx_mul]
      show Glob.reidx (mR (y' * y'⁻¹)) = 1
      rw [mul_inv_cancel]; exact DenseP.reidx_one
    calc (mat (γ * (ι y')⁻¹)).map (psiT D τ)
        = (mat (γ * (ι y')⁻¹)).map (psiT D τ) * (Glob.reidx (mR y') * Glob.reidx (mR y'⁻¹)) := by
          rw [h2, Matrix.mul_one]
      _ = 1 := by rw [← Matrix.mul_assoc, ← h1, h2]
  generalize γ * (ι y')⁻¹ = x at hR ⊢
  apply Subtype.ext
  apply Units.ext
  show mat (x * ι y'') = mat (ι y'' * x)
  rw [DenseP.mat_mul, DenseP.mat_mul]
  apply Formalism.IndefR.Eqv.mat_ext D
  · intro τ'
    rw [Matrix.map_mul, Matrix.map_mul]
    by_cases h : τ' = τ
    · subst h; rw [hR]; simp only [Matrix.one_mul, Matrix.mul_one]
    · have h1 : (mat (ι y'')).map (psiT D τ') = 1 := by rw [← hc]; exact (hι.2 y'').2.1 τ' h
      rw [h1]; simp only [Matrix.one_mul, Matrix.mul_one]
  · rw [Matrix.map_mul, Matrix.map_mul, (hι.2 y'').2.2]; simp only [Matrix.one_mul, Matrix.mul_one]

end PositivityTheory.Rg.Sw.Glob
