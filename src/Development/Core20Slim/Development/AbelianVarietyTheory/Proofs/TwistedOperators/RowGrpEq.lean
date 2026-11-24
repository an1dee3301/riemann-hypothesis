module

public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealLineOfPeriodsOnLine
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoefProd
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsGLSubmatrix
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsDatOfTower
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompProjAnisotropicAnisotropicEmbedding
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsOrthDec
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsWeilDatumAnisotropicKernelPair
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowBesZeroE
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Int.DivMod.Basic
public import Init.Data.Int.DivMod.Bootstrap
public import Init.Data.Int.Lemmas
public import Init.Data.Int.Order
public import Init.Data.List.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Order.Lemmas
public import Init.Data.Zero
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Defs
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Notation
public import Mathlib.Order.RelClasses

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped NNReal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.CellMass

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc)

def rowN (j : ℕ) : Subgroup (GA D (G.V (.grid D.R.m j))) :=
  if h : j + 2 * ((D.R.m - 1 - j) / 2) + 1 = D.R.m then GlobalTheory.MixPer.flagN (rowJac G j (by omega) ((D.R.m - 1 - j) / 2) (by omega))
  else if h' : j + 2 * ((D.R.m - 2 - j) / 2) + 2 = D.R.m then GlobalTheory.MixPer.flagN (besDecAt G j _ h') else ⊥

def rowEmb (j : ℕ) : GA D (G.V (.top j)) →* GA D (G.V (.grid D.R.m j)) :=
  if h : j + 2 * ((D.R.m - 1 - j) / 2) + 1 = D.R.m then (rowJac G j (by omega) ((D.R.m - 1 - j) / 2) (by omega)).emb0
  else if h' : j + 2 * ((D.R.m - 2 - j) / 2) + 2 = D.R.m then
    GlobalTheory.MixPer.embA (besDecAt G j _ h') (GlobalTheory.OrthSumExists.orthDecHsum D _ _) else 1

theorem rowGrp_eq (j : ℕ) : rowGrp G j = rowN G j ⊔ (rowEmb G j).range := by
  unfold rowGrp rowN rowEmb
  split_ifs
  · rfl
  · rfl
  · simp

def prSet (j : ℕ) (b : GfC (G.V (.grid D.R.m j))) : Set (GfC (G.V (.top j))) :=
  {g | ∃ n ∈ rowN G j, (b.1)⁻¹ * (n * rowEmb G j g.1) * b.1 ∈ latGrp G j}

end GlobalTheory.CellMass
