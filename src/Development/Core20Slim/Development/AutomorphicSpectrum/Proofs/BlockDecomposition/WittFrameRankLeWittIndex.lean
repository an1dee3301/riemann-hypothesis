module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.LintegralSiegelConeInvModulusLtTopWeilStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FoundationProofs.WittIdxOfParallelSig
public import Development.Core20Slim.Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.FirstClauseRankZero
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SatakeDualWeyl.Statement
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
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
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Range
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.SesquilinearForm.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Defs
public import Mathlib.Order.Lattice.Nat
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal

@[expose] public section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.SiegelFormula
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.WittFrame

open Matrix

theorem length_le_wittIdx (D : D7) (V : HSp D) {r : ℕ} (Xf Yf : Matrix (Fin V.rank) (Fin r) D.host.E)
    (hW : GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram Xf Yf) : r ≤ Formalism.MainNotions.SchurIrreducible.wittIdx V := by
  have hc : ∀ {a : ℕ} (A : Matrix (Fin V.rank) (Fin a) D.host.E),
      Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) A = Aᴴ := by
    intro a A
    exact Matrix.ext fun i j => rfl
  have hxx : Xfᴴ * V.gram * Xf = 0 := by rw [← hc]; exact hW.xx
  have hxy : Xfᴴ * V.gram * Yf = 1 := by rw [← hc]; exact hW.xy
  have hG : V.gramᴴ = V.gram := by
    refine Matrix.ext fun a b => ?_
    exact V.herm.eq _ _
  have hyx : Yfᴴ * V.gram * Xf = 1 := by
    have h := congrArg conjTranspose hxy
    simpa [conjTranspose_mul, hG, Matrix.mul_assoc] using h
  let f : (Fin r → D.host.E) →ₗ[D.host.E] V.V := V.frame.equivFun.symm.toLinearMap.comp Xf.mulVecLin
  have hf : Function.Injective f := by
    refine V.frame.equivFun.symm.injective.comp (g := V.frame.equivFun.symm) (f := Xf.mulVec) fun v w hvw => ?_
    have := congrArg (Yfᴴ * V.gram).mulVec hvw
    simpa [mulVec_mulVec, hyx] using this
  refine le_csSup (GlobalTheory.SiegelFormula.Model.bddAbove_witt V) ⟨LinearMap.range f, by simpa using LinearMap.finrank_range_of_inj hf, ?_⟩
  rintro _ ⟨v, rfl⟩ _ ⟨w, rfl⟩
  change V.hT (V.frame.equivFun.symm (Xf *ᵥ v)) (V.frame.equivFun.symm (Xf *ᵥ w)) = 0
  rw [GlobalTheory.ParallelWitt.form_eq, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, hxx]
  simp

end GlobalTheory.CompanionTheory.WittFrame
