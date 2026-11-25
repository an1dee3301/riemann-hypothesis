module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.NodeAgree
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
public import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqExistsIffDsExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeCharIsUnitaryOfUnitaryInfinityTypeStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Definitions.Divisors.LeastSplitAuxiliaryPrimeThetaChainSpec
public import Development.AbelianVarietyTheory.Definitions.Foundations.StrictInterlaceIffDescEnum
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NodeYPredEqChainVertexAtRowZeroLast
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.Divisibility.LiftLat
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemSum
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.UnitaryNorms.CharHost
public import Formalism.LocalToGlobal.UnitaryNorms.CharTied
public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.Ring.Unbundled.Rat
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Rat.Floor
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Grid

theorem heckeCharacterGrid_isAuxiliaryCharacter_testGrid_alt : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : GlobalTheory.ChiGrid.Consts}, GlobalTheory.Grid.gap D = GlobalTheory.ChiGrid.gap D 1 → sc.cGap = 1 → ∀ {G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc} (Z : GlobalTheory.Grid.PlaceDat D), Z.S0 R.Pg = G'.pl.S0 → (∀ w, w ∈ R.Pg ∨ w ∈ Z.Wd → w.under (𝓞 D.host.F) ∈ GlobalTheory.ChiGrid.S1 D) → (∀ w ∈ Z.Wd, Formalism.L2.Host.OverP D.host D.host.pde w ∨ Formalism.L2.Host.OverP D.host D.host.pde' w) → Z.w0 = G'.pl.w G'.pl.v0 → ∀ i, 1 ≤ i → i ≤ D.R.m → Z.IsGridPlaceAuxiliaryHeckeCharacter R.Pg (fun τ => GlobalTheory.Grid.cen D τ i) (G'.ch.chiH i) := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R sc hgap hc G' Z hS0 hS1 hwd hw0 i hi1 hi2
  have hcen : ∀ τ, GlobalTheory.Grid.cen D τ i = GlobalTheory.ChiGrid.cen D sc.cGap τ i := by
    intro τ
    rw [hc]
    unfold GlobalTheory.Grid.cen GlobalTheory.ChiGrid.cen GlobalTheory.Grid.gridOf
    rw [hgap]
    rfl
  have hunit : (G'.ch.chiH i).IsUnitary := GlobalTheory.T.heckeChar_isUnitary_of_unitary_infinityType _ _ _ _ (G'.ch.inf i hi1 hi2)
  refine ⟨hunit, G'.ch.triv i hi1 hi2, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨fun τ => 2 * GlobalTheory.ChiGrid.cen D sc.cGap τ i, fun τ => ?_, G'.ch.inf i hi1 hi2⟩
    show ((2 * GlobalTheory.ChiGrid.cen D sc.cGap τ i : ℤ) : ℚ) = 2 * ((GlobalTheory.Grid.cen D τ i : ℤ) : ℚ)
    rw [hcen τ]; push_cast; ring
  · intro w hw
    rw [hS0] at hw
    exact G'.ch.unr i hi1 hi2 w hw
  · intro w hw
    exact G'.ch.lev1 i hi1 hi2 w (hS1 w hw)
  · intro w hw x hx
    exact G'.ch.wild i hi1 hi2 w (hwd w hw) x hx
  · have hu : Z.w0.under (𝓞 D.host.F) = G'.pl.v0 := by
      rw [hw0]; exact G'.pl.under_w (G'.pl.mem_S0_of_sum_eq.2 (Or.inl rfl))
    exact G'.ch.lev0 i hi1 hi2 Z.w0 hu

end GlobalTheory.Grid

end
