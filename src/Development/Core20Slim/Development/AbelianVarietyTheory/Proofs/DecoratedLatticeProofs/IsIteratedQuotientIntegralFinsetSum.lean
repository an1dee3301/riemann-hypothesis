module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PeriodSumHolds
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacuaStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlacewiseToAdelicDecompositionForall
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaFunctionProductsSlicesOrthogonalDecompositi
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HandBFSmul
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BilinearVacuumCentralCharacter
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatThetaMapsPreserveThetaFunctions
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatThetaMapsConvergeThetaFunctionsStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselThetaContractionExtendByZeroVacuumSmoothStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleStepEqTwoThetaColumnLifts
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationTwoVariableModelAndLineExte
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Classical
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Lattice.Basic
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Set.Defs
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Vac Moves InK Lat Pl latV idAt idOff intAt grpAt grpOff MxAt hand0 SplitPt extS extT)

noncomputable section
namespace GlobalTheory.QLawPf

section Iter
variable {G₁ G₂ : Type} [Group G₁] [MeasurableSpace G₁] [TopologicalSpace G₁] [Group G₂] [MeasurableSpace G₂]
    [TopologicalSpace G₂] {R₁ : Subgroup G₁} {R₂ : Subgroup G₂} {ρ₁ : Measure R₁} {μ₁ : Measure G₁} {ρ₂ : Measure R₂}
    {μ₂ : Measure G₂}



end Iter

variable {D : D7}

theorem moves_iff_forall {S : HSp D} {L : Lat S} (hL : IsSelfDualC S L) (P : Pl D → Prop) (g : GA D S) :
    Moves S g L L P ↔ ∀ v, P v → Moves S g L L (· = v) := by
  have hP := fun z => ((GlobalTheory.T.adelicPoint_components_atPlaces_lattices_vacua D P).2 S).2.2.2 L z hL.1
  have hmv := fun (R : Pl D → Prop) (y : Fin S.rank → AE D) (hy : ∀ i, y i ∈ idAt D R) =>
    GlobalTheory.FinPl.PlacesAdeles.supp_mulVec S R g hy
  constructor
  · intro h v hv y hy
    have key : ∀ z : Fin S.rank → AE D, (∀ i, z i ∈ idAt D (· = v)) → (z ∈ latV S L P ↔ z ∈ latV S L (· = v)) := by
      intro z hz
      rw [hP, ((GlobalTheory.T.adelicPoint_components_atPlaces_lattices_vacua D (· = v)).2 S).2.2.2 L z hL.1]
      constructor
      · rintro ⟨_, h⟩
        exact ⟨hz, fun w hw e he => h w (hw ▸ hv) e he⟩
      · rintro ⟨_, h⟩
        refine ⟨fun i => GlobalTheory.FinPl.PlacesAdeles.idAt_single_le hv (hz i), fun w _ e he => ?_⟩
        by_cases hwv : w = v
        · exact h w hwv e he
        · obtain ⟨ε, -, -, -, hAt, hOff⟩ := (GlobalTheory.T.adelicPoint_components_atPlaces_lattices_vacua D (· = w)).1
          have hzero : e • z = 0 := by
            funext i
            have h1 : ε * e = e := (hAt e).1 he.1
            have h2 : ε * z i = 0 := (hOff (z i)).1 (GlobalTheory.FinPl.PlacesAdeles.idAt_le_idOff hwv (hz i))
            show e * z i = 0
            rw [← h1, mul_comm ε e, mul_assoc, h2, mul_zero]
          rw [hzero]
          exact (latV S L (· = w)).zero_mem
    rw [← key y hy, ← key _ (hmv _ y hy)]
    exact h y fun i => GlobalTheory.FinPl.PlacesAdeles.idAt_single_le hv (hy i)
  · intro h y hy
    rw [hP y, hP (mt S g *ᵥ y)]
    constructor
    · rintro ⟨_, hy'⟩
      refine ⟨hmv _ y hy, fun w hw e he => ?_⟩
      have hey : ∀ i, (e • y) i ∈ idAt D (· = w) := fun i => Ideal.mul_mem_right _ _ he.1
      rw [← Matrix.mulVec_smul]
      exact (h w hw (e • y) hey).1 (hy' w hw e he)
    · rintro ⟨_, hy'⟩
      refine ⟨hy, fun w hw e he => ?_⟩
      have hey : ∀ i, (e • y) i ∈ idAt D (· = w) := fun i => Ideal.mul_mem_right _ _ he.1
      refine (h w hw (e • y) hey).2 ?_
      rw [Matrix.mulVec_smul]
      exact hy' w hw e he


variable {ψ : AddChar (AF D.host.F) ℂ}














section Step
variable {σ : ℕ} (S : Dbl2 ψ σ)


variable {S}






end Step

end GlobalTheory.QLawPf
end
