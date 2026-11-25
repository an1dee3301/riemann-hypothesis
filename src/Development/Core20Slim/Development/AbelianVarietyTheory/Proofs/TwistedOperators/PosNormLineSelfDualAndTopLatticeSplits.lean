module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.TiltSc
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.TopOrthEmb
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SumMatApply
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OrthAtSumLatO
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSelfDualCOfGramOne
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalVolumeLift
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsRatDatum
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ContinuousResTSymm
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
public import Formalism.LocalToGlobal.Divisibility.LiftLat
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Fin.Basic
public import Init.Data.Int.Basic
public import Init.Data.List.Basic
public import Init.Data.List.FinRange
public import Init.Data.Nat.Basic
public import Init.Data.NeZero
public import Init.Data.Zero
public import Init.Prelude
public import Init.PropLemmas
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.FractionalIdeal.Basic
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowShape

variable {D : D7}

theorem pLine_gram_eq_one : (pLine D).gram = 1 := by
  rw [pLine_gram]
  ext i j
  fin_cases i; fin_cases j
  simp [antiDiagonalSignGramMatrix]
  rfl

theorem mem_topL_iff (z : Fin (pLine D).rank → D.host.E) : z ∈ topL D ↔ z ∈ GlobalTheory.AdForm.intVec D (pLine D).rank := by
  simp only [topL, latPi, Submodule.mem_pi, Set.mem_univ, true_implies, FractionalIdeal.coe_one, Submodule.mem_one]
  show _ ↔ ∀ k, IsIntegral ℤ (z k)
  refine forall_congr' fun k => ⟨?_, fun h => ⟨⟨z k, h⟩, rfl⟩⟩
  rintro ⟨b, hb⟩
  rw [← hb]
  exact b.2

theorem isSelfDualC_topL : IsSelfDualC (pLine D) (topL D) :=
  GlobalTheory.LocMod.IntFrameStd.isSelfDualC_of_gram_one pLine_gram_eq_one _ mem_topL_iff

variable {T : Type} {L : LevCh D T} {sc : Consts}

theorem topLat_eq_sumLatO (G : GridData L sc) :
    G.Λ (.top D.R.m) = GlobalTheory.Core.Rk.SumBox.sumLatO (topOrth G) (G.Λ (.grid D.R.m D.R.m)) (topL D) := by
  have e : G.Λ (.top D.R.m) = G.sp.topDec.lat (G.Λ (.grid D.R.m D.R.m)) (fun _ => 1) := G.sp.topLat
  rw [e]
  ext x
  rw [GlobalTheory.Core.Rk.SumBox.mem_sumLatO]
  constructor
  · rintro ⟨y, hy, u, hu, rfl⟩
    exact ⟨y, hy, u, Submodule.mem_pi.2 fun p _ => hu p, rfl⟩
  · rintro ⟨y, hy, u, hu, rfl⟩
    exact ⟨y, hy, u, fun p => Submodule.mem_pi.1 hu p (Set.mem_univ _), rfl⟩

theorem topLat_orthAt (G : GridData L sc) (v : Pl D) :
    OrthAt (topOrth G) (G.Λ (.top D.R.m)) (G.Λ (.grid D.R.m D.R.m)) (topL D) v := by
  rw [topLat_eq_sumLatO G]
  exact GlobalTheory.Core.Rk.SumSplit.orthAt_sumLatO D _ _ _ (topOrth G) _ _ v

theorem topL_selfDual_orthAt : Big fun {D} {Γ} _ _ {Pl0 T} {A} {Ks} _ _ _ {R} ch => IsSelfDualC _ (GlobalTheory.RowShape.topL D) ∧
    ∀ v, GlobalTheory.FinPl.OrthAt (topOrth ch.G) (ch.G.Λ (.top D.R.m)) (ch.G.Λ (.grid D.R.m D.R.m)) (GlobalTheory.RowShape.topL D) v :=
  ⟨0, fun _ _ _ => ⟨0, fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ch _ _ =>
    ⟨isSelfDualC_topL, fun v => topLat_orthAt ch.G v⟩⟩⟩

end GlobalTheory.RowShape
end
