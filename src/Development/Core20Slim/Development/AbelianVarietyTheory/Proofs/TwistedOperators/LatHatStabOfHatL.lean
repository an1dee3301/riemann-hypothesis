module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairPtsClasses
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairPtsEqSum
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.MovFn
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.DetIdlVal
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugatedLevelElementKeepsStandardLattice
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceColumnMemCompletedLatticeIffFrameInteg
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.InvVolConjLevelOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Formalism.LocalToGlobal.HermitianColumns.InLocalDiscriminantKernel
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.SatakeDualWeyl.Statement
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.Order.Basic
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Maps

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.RowVertexInv GlobalTheory.SplitFlip
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.RowVacScalar

noncomputable section

open scoped TensorProduct

namespace GlobalTheory.RowMovedLat

open Matrix

variable {D : D7}

theorem negGA_mem_GfC (V : HSp D) {g : GA D V} (hg : g ∈ GfC V) : negGA V g ∈ GfC (negSp V) := by
  have e : matHom (negSp V) (negGA V g) = matHom V g := Units.ext (mt_negGA V g)
  simp only [GfC, MonoidHom.mem_ker, infHom, MonoidHom.comp_apply] at hg ⊢
  rw [e]
  exact hg

theorem latHat_stab_of_hatL (V : HSp D) (g : GA D V) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (h : ∀ z, z ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ ↔
      (Formalism.IndefR.Lev.finE V g).val *ᵥ z ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ)
    (y : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) :
    y ∈ latHat D.host.F D.host.E (Λ : Set (Fin V.rank → D.host.E)) ↔
      ((Formalism.L2.Theta.mt V g).map (finPart D)).mulVec y ∈ latHat D.host.F D.host.E (Λ : Set (Fin V.rank → D.host.E)) := by
  have key : (fun i => Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E
      ((((Formalism.L2.Theta.mt V g).map (finPart D)).mulVec y) i)) =
      (Formalism.IndefR.Lev.finE V g).val *ᵥ (fun i => Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E (y i)) := by
    have hf : (Formalism.IndefR.Lev.finE V g).val = ((Formalism.L2.Theta.mt V g).map (finPart D)).map (Formalism.IndefR.Lev.swapAE D) := by
      ext i j
      rfl
    rw [hf]
    ext i
    exact RingHom.map_mulVec (Formalism.IndefR.Lev.swapAE D) _ y i
  refine (GlobalTheory.SplitFrameColumn.latHat_iff_hatL Λ y).trans ((h _).trans ?_)
  refine Iff.symm ((GlobalTheory.SplitFrameColumn.latHat_iff_hatL Λ _).trans ?_)
  exact Iff.of_eq (congrArg (· ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ) key)

end GlobalTheory.RowMovedLat

namespace GlobalTheory.RowMovedLat

theorem moved_pair_stab : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}
    (S : GridChoice W U) {t : T}, t ∈ U → ∀ (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.grid (j + 1) D.R.m)),
    finG (G.V (.grid (j + 1) D.R.m)) k ∈ S.levRow t (j + 1) hj.le →
    (G.toPair (.chi j D.R.m) 1 (moved S j k)).1 ∈ GfC (G.pS (.chi j D.R.m)) ∧
    (∀ y, y ∈ latHat D.host.F D.host.E (S.N.latS (.chi j D.R.m) : Set (Fin (G.pS (.chi j D.R.m)).rank → D.host.E)) ↔
      ((Formalism.L2.Theta.mt _ (G.toPair (.chi j D.R.m) 1 (moved S j k)).1).map (finPart D)).mulVec y ∈
        latHat D.host.F D.host.E (S.N.latS (.chi j D.R.m) : Set (Fin (G.pS (.chi j D.R.m)).rank → D.host.E))) ∧
    (G.toPair (.chi (j + 1) D.R.m) (moved S j k) 1).2 ∈ GfC (G.pT (.chi (j + 1) D.R.m)) ∧
    (∀ y, y ∈ latHat D.host.F D.host.E (S.N.latT (.chi (j + 1) D.R.m) : Set (Fin (G.pT (.chi (j + 1) D.R.m)).rank → D.host.E)) ↔
      ((Formalism.L2.Theta.mt _ (G.toPair (.chi (j + 1) D.R.m) (moved S j k) 1).2).map (finPart D)).mulVec y ∈
        latHat D.host.F D.host.E (S.N.latT (.chi (j + 1) D.R.m) : Set (Fin (G.pT (.chi (j + 1) D.R.m)).rank → D.host.E))) := by
  intro D T L sc G W U S t _ j hj k hk
  have hG : moved S j k ∈ GfC (G.V (.grid (j + 1) D.R.m)) :=
    (((S.N.u (.grid (j + 1) D.R.m))⁻¹ * k * S.N.u (.grid (j + 1) D.R.m) : FinPt G (.grid (j + 1) D.R.m))).2
  have hst := latHat_stab_of_hatL _ (moved S j k) _ (moved_keeps_std S j hj k hk)
  exact ⟨negGA_mem_GfC _ hG, hst, hG, hst⟩

end GlobalTheory.RowMovedLat

end
