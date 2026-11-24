module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevRowSuccInfUA
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridRowLevelZeroInfUnitaryEqDatumLevelStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Definitions.Divisors.BplusOfEquivariant
public import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.InvVolConjLevelOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
public import Development.Core20Slim.Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataParams₂
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.Divisibility.LiftLat
public import Formalism.LocalToGlobal.HermitianColumns.InLocalDiscriminantKernel
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Int.Lemmas
public import Init.Data.Int.Order
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowLevelUnit

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}

theorem levJ_grid_succ (G : GridData L sc) (t : T) (i n : ℕ) (hn : n ≠ 0) :
    levJ G t (.grid (i + 1) n) = G.levMax (.grid (i + 1) n) := by
  cases n with
  | zero => exact absurd rfl hn
  | succ n => rfl

theorem levJ_grid_zero (G : GridData L sc) (t : T) (n : ℕ) (hn : n ≠ 0) :
    HEq (levJ G t (.grid 0 n)) (levCol L t (n - 1)) := by
  cases n with
  | zero => exact absurd rfl hn
  | succ n => exact HEq.rfl

theorem levRow_iff_levJ : Big fun {D} _ _ _ _ _ _ _ _ _ _ _ ch => ∀ t i (hi : i ≤ D.R.m) (k : FinPt ch.G (.grid i D.R.m)), finG (ch.G.V (.grid i D.R.m)) k ∈ ch.S.toGridChoice.levRow t i hi ↔ finG (ch.G.V (.grid i D.R.m)) k ∈ levJ ch.G t (.grid i D.R.m) :=
  ⟨0, fun _ _ _ => ⟨0, fun D _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s ch _ _ t i hi k => by
    have hm : D.R.m ≠ 0 := by have := D.R.two_le_m; omega
    have hU : finG (ch.G.V (.grid i D.R.m)) k ∈ UA D.sp.cm (ch.G.V (.grid i D.R.m)).gram := GlobalTheory.LevSplit.finE_mem_UA _ _
    suffices e : ch.S.toGridChoice.levRow t i hi ⊓ UA D.sp.cm (ch.G.V (.grid i D.R.m)).gram = levJ ch.G t (.grid i D.R.m) by
      rw [← e]; exact ⟨fun h => ⟨h, hU⟩, fun h => h.1⟩
    clear hU k
    cases i with
    | zero =>
      apply eq_of_heq
      exact (GlobalTheory.T.gridRowLevel_zero_inf_unitary_eq_datumLevel ch.W ch.S.toGridChoice s.core.lev t hi).trans
        ((levJ_grid_zero ch.G t D.R.m hm).trans (levCol_top _ t (j := D.R.m - 1) (by omega))).symm
    | succ i =>
      rw [levJ_grid_succ ch.G t i D.R.m hm]
      exact GlobalTheory.FunObj.GridChoice.levRow_succ_inf_UA ch.W ch.S.toGridChoice t i hi⟩⟩

end GlobalTheory.RowLevelUnit
