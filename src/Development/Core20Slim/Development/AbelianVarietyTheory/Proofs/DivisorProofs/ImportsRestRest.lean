module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMixModelB
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAwayUnitOfPowEqOne
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.VolIntegrableOnIff
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Definitions.Divisors.BplusOfEquivariant
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.Divisors.ExistsBplusNeZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Classical
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Torsor.Defs
public import Mathlib.Basic.Countable.Defs
public import Mathlib.Basic.ENNReal.Action
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.ENNReal.Operations
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.NNReal.Basic
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Module
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.MeasureTheory.OuterMeasure.Basic
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Notation
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Closure
public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Order
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.Sets.Compacts

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory Matrix
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm GlobalTheory.BigNZ GlobalTheory.FlipMatch GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB incM)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW psiLoc chrW)
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopFlip

namespace GlobalTheory.TopFlip.MeasW

theorem nu_eq {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {t t' : T} {M M' : Vol G}
    (hM : M.Is t) (hM' : M'.Is t') (i j : Fin D.R.m) :
    M.ν (.grid (i + 1) (j + 1)) = M'.ν (.grid (i + 1) (j + 1)) :=
  GlobalTheory.FunObjModel.isAt_unique (hM.vtx (.grid (i + 1) (j + 1)) ⟨i.2, j.2⟩) (hM'.vtx (.grid (i + 1) (j + 1)) ⟨i.2, j.2⟩)

theorem exists_ratio : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ (i j : Fin D.R.m) (m : Measure (GA D (spW G i j))), m.IsHaarMeasure →
      ∃ s₀ : NNReal, s₀ ≠ 0 ∧ ∀ (t : T) (M : Vol G), M.Is t → ∀ s : NNReal, M.ν (.grid (i + 1) (j + 1)) = s • m → s = s₀ := by
  intro D T L sc G μ₀ _ i j m hm
  by_cases h : ∃ (t : T) (M : Vol G) (s : NNReal), M.Is t ∧ M.ν (.grid (i + 1) (j + 1)) = s • m
  · obtain ⟨t₀, M₀, s₀, hM₀, e₀⟩ := h
    have hH := (hM₀.vtx (.grid (i + 1) (j + 1)) ⟨i.2, j.2⟩).haar_fund.1
    obtain ⟨a1, a2, a3, a4, a5, -, a7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D (spW G i j)
    obtain ⟨K⟩ : Nonempty (TopologicalSpace.PositiveCompacts (GA D (spW G i j))) := inferInstance
    have hK0 : m K ≠ 0 :=
      ((isOpen_interior.measure_pos m K.interior_nonempty).trans_le (measure_mono interior_subset)).ne'
    have hK1 : m K ≠ ⊤ := K.isCompact.measure_lt_top.ne
    refine ⟨s₀, ?_, fun t M hM s e => ?_⟩
    · rintro rfl
      rw [e₀, zero_smul] at hH
      exact (isOpen_univ.measure_pos (0 : Measure (GA D (spW G i j))) Set.univ_nonempty).ne' rfl
    · have e1 : s • m = s₀ • m := e.symm.trans ((nu_eq hM hM₀ i j).trans e₀)
      have e2 : (s : ENNReal) * m K = (s₀ : ENNReal) * m K := by
        have e3 := congrArg (fun μ : Measure (GA D (spW G i j)) => μ K) e1
        exact e3
      exact_mod_cast (ENNReal.mul_left_inj hK0 hK1).1 e2
  · exact ⟨1, one_ne_zero, fun t M hM s e => absurd ⟨t, M, s, hM, e⟩ h⟩

end GlobalTheory.TopFlip.MeasW

end
