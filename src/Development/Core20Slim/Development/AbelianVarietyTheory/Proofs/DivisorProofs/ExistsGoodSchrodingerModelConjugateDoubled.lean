module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareStanding
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateUnitaryAdelicIsoMapHaarAndFundamentalDoStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalDarbouxCoordinatesTensorHermitianStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallySelfDualLatticeIndicatorIsVacuumStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinitePlaceVacuumAnyDarbouxCoordinatesStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Definitions.Divisors.BplusOfEquivariant
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
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
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Prod
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Notation.Indicator
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Module
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Filter.Cofinite
public import Mathlib.Order.Filter.Defs
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Instances.Matrix

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.SquareModel

theorem exists_isGood_model_conj : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (_hL : L.Is μ₀) (t : T)
    (i j : Fin D.R.m) (M : Vol G), M.Is t → ∀ (B : Base D.host.F D.host.E), B.IsGood D.sp.cm.sig →
    ∀ (X : Spc D.host.F D.host.E (spW G i j).rank) (Y : Spc D.host.F D.host.E ((spW G i j).rank + (spW₁ G i j).rank))
      (hJ : X.J = (1 : D.host.E) • (spW G i j).gram) (r s r' s' : ℕ),
      X.IsHerm D.sp.cm.sig B r s → Y.IsSkew D.sp.cm.sig B r' s' →
      ∃ co vac dom, Model.IsGood (Model.mk (σ := D.sp.cm.sig) (X := X) (W := Y) co vac ((M.ν (.grid ((i : ℕ) + 1) ((j : ℕ) + 1))).map (conjU _ 1 hJ)) dom) B.ψ := by
  intro D T L sc G μ₀ _hL t i j M hM B hB X Y hJ r s r' s' hX hY
  obtain ⟨hH, hfd⟩ := (hM.vtx (.grid ((i : ℕ) + 1) ((j : ℕ) + 1)) ⟨i.2, j.2⟩).haar_fund
  obtain ⟨hH', hfd'⟩ := GlobalTheory.T.conjugateUnitaryAdelicIso_map_haar_and_fundamentalDomain _ (1 : D.host.E) one_ne_zero hJ _ _ hH hfd
  obtain ⟨co, hrat⟩ := GlobalTheory.T.exists_rational_darboux_coordinates_tensor_hermitian B hB X Y r s r' s' hX hY
  have hind := GlobalTheory.T.eventually_selfDualLattice_indicator_is_vacuum B hB X Y r s r' s' hX hY co hrat
  have hany := GlobalTheory.T.exists_finitePlace_vacuum_any_darboux_coordinates B hB X Y r s r' s' hX hY co
  let ind : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := D.host.F), (Fin (spW G i j).rank × Fin ((spW G i j).rank + (spW₁ G i j).rank) → Fv D.host.F v) → ℂ :=
    fun v => Set.indicator {x | ∀ k, x k ∈ v.adicCompletionIntegers D.host.F} 1
  let vac : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := D.host.F), (Fin (spW G i j).rank × Fin ((spW G i j).rank + (spW₁ G i j).rank) → Fv D.host.F v) → ℂ :=
    fun v => if Model.IsVac (Model.mk (σ := D.sp.cm.sig) (X := X) (W := Y) co (fun _ => 0) 0 ∅) B.ψ v (ind v) then ind v
      else (hany v).choose
  refine ⟨co, vac, _, { rat := hrat, vac := fun v => ?_, std := ?_, haar := hH', dom := hfd' }⟩
  · show Model.IsVac (Model.mk (σ := D.sp.cm.sig) (X := X) (W := Y) co (fun _ => 0) 0 ∅) B.ψ v (vac v)
    by_cases h : Model.IsVac (Model.mk (σ := D.sp.cm.sig) (X := X) (W := Y) co (fun _ => 0) 0 ∅) B.ψ v (ind v)
    · simp only [vac, if_pos h]; exact h
    · simp only [vac, if_neg h]; exact (hany v).choose_spec
  · filter_upwards [hind] with v hv
    show vac v = ind v
    exact if_pos hv

end GlobalTheory.SquareModel
