module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicHeightBlockDiagonalEmbeddingLeMul
public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

noncomputable section
namespace GlobalTheory.Grow.IoHeight

theorem height_io_le (D : D7) (A : HSp D) (g₁ g₂ : GA D A) :
    GlobalTheory.Grow.height (dblSp A) (io A (g₁, g₂)) ≤ GlobalTheory.Grow.height A g₁ * GlobalTheory.Grow.height A g₂ := by
  have h := GlobalTheory.BlockHeight.heightGL_blk_le D.host.F (finSumFinEquiv (m := A.rank) (n := A.rank))
    (Formalism.L2.Theta.matHom (dblSp A) (io A (g₁, g₂))) (Formalism.L2.Theta.matHom A g₁) (Formalism.L2.Theta.matHom A g₂) rfl rfl
  show ((GlobalTheory.AdelicU.heightGL D.host.F _ : ℝ≥0) : ℝ) ≤ ((GlobalTheory.AdelicU.heightGL D.host.F _ : ℝ≥0) : ℝ) * ((GlobalTheory.AdelicU.heightGL D.host.F _ : ℝ≥0) : ℝ)
  exact_mod_cast h

theorem main : ∀ (D : D7) (A : HSp D), ∃ (C : ℝ) (c : ℕ), ∀ g₁ g₂ : GA D A, GlobalTheory.Grow.height (dblSp A) (io A (g₁, g₂)) ≤ C * (GlobalTheory.Grow.height A g₁ * GlobalTheory.Grow.height A g₂) ^ c :=
  fun D A => ⟨1, 1, fun g₁ g₂ => by simpa using height_io_le D A g₁ g₂⟩

end GlobalTheory.Grow.IoHeight
end
