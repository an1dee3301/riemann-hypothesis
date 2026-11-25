module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstRowVertexWeilValue
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
public import Development.Core20Slim.Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.EndomorphismLawFromFirstRowTwist
public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.StepUnfold
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairPtsClasses
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowMapVUpdateZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.InvVolConjLevelOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.EdgeFactorNeZero
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
public import Formalism.LocalToGlobal.IndefiniteReal.Bridge
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Notation.Pi.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Sets
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Logic.Function.Basic
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section
namespace GlobalTheory.FirstRowTermLaw
end GlobalTheory.FirstRowTermLaw
namespace GlobalTheory.FirstRowTermLaw
set_option maxHeartbeats 1000000 in
theorem lift_splits_locally : FunPr.ThetaLocalInputs → SumOKK → Big fun {D} {_Γ} _ _ {_Pl0} {T} {_A} {_Ks} _ _ _ {R} ch =>
    ∀ (t : T) a, ∀ β ∈ ch.S.supp t (ch.Phi a), ∀ τ, ch.S.IsExpansion t (ch.Phi a) β τ →
    ∀ (k : FinPt ch.G (.grid 0 D.R.m)), finG (ch.G.V (.grid 0 D.R.m)) k ∈ ch.S.levRow t 0 (Nat.zero_le _) →
    ∀ (hk : toXf k ∈ (levEnv D.sp.X' R.βX (R.datXt t)).J) (c : ℂ),
      ch.W.om (.chi (FirstRowVertex.firstIx D) D.R.m : Pair T) (ch.G.toPair (.chi (FirstRowVertex.firstIx D) D.R.m : Pair T) ((ch.S.N.u (.grid 0 D.R.m))⁻¹ * k * ch.S.N.u (.grid 0 D.R.m)).1 1) (ch.S.Z.vac (.chi (FirstRowVertex.firstIx D) D.R.m : Pair T)) = c • ch.S.Z.vac (.chi (FirstRowVertex.firstIx D) D.R.m : Pair T) →
    ∀ (xs : ∀ j : Fin D.R.m, WO (ch.G.pS (.top t j)) (ch.G.pT (.top t j)))
      (ys : ∀ i : Fin D.R.m, WO (ch.G.pS (.chi i D.R.m : Pair T)) (ch.G.pT (.chi i D.R.m : Pair T))),
      (((levEnv D.sp.X' R.βX (R.datXt t)).χ ⟨toXf k, hk⟩ : ℂˣ) : ℂ) * c *
        (τ.sum fun d a' => a' * (∏ j, (d.1 j).fn (xs j)) *
          ∏ i, Function.update (fun i => (d.2 i).fn) (FirstRowVertex.firstIx D)
            (fun y => (d.2 (FirstRowVertex.firstIx D)).fn (actO (ch.G.pS (.chi (FirstRowVertex.firstIx D) D.R.m : Pair T)) (ch.G.pT (.chi (FirstRowVertex.firstIx D) D.R.m : Pair T)) (ch.G.toPair (.chi (FirstRowVertex.firstIx D) D.R.m : Pair T) ((ch.S.N.u (.grid 0 D.R.m))⁻¹ * k * ch.S.N.u (.grid 0 D.R.m)).1 1).1⁻¹ (ch.G.toPair (.chi (FirstRowVertex.firstIx D) D.R.m : Pair T) ((ch.S.N.u (.grid 0 D.R.m))⁻¹ * k * ch.S.N.u (.grid 0 D.R.m)).1 1).2⁻¹ y)) i (ys i)) =
      τ.sum fun d a' => a' * (∏ j, (d.1 j).fn (xs j)) * ∏ i, (d.2 i).fn (ys i) := by
  intro hP hS
  obtain ⟨a₁, h₁⟩ := _root_.GlobalTheory.T.endomorphism_law_from_first_row_twist hP hS
  refine ⟨a₁, fun ε CF hC => ?_⟩
  obtain ⟨x₁, hc₁⟩ := h₁ ε CF hC
  refine ⟨x₁, ?_⟩
  intro D large₂ e hx Γ _ _ Pl0 T A Ks _ _ _ R F s ch hi hsc t a β hβ τ hτ k hkl hk c hc xs ys
  obtain ⟨lam, hlam, hscal⟩ := hc₁ D large₂ e hx Γ Pl0 T A Ks R F s ch hi hsc t a k hkl hk c hc
  have hL : (τ.sum fun d a' => a' * (∏ j, (d.1 j).fn (xs j)) *
      ∏ i, Function.update (fun i => (d.2 i).fn) (FirstRowVertex.firstIx D) (fun y => (d.2 (FirstRowVertex.firstIx D)).fn ((actO (ch.G.pS (.chi (FirstRowVertex.firstIx D) D.R.m : Pair T)) (ch.G.pT (.chi (FirstRowVertex.firstIx D) D.R.m : Pair T)) (ch.G.toPair (.chi (FirstRowVertex.firstIx D) D.R.m : Pair T) ((ch.S.N.u (.grid 0 D.R.m))⁻¹ * k * ch.S.N.u (.grid 0 D.R.m)).1 1).1⁻¹ (ch.G.toPair (.chi (FirstRowVertex.firstIx D) D.R.m : Pair T) ((ch.S.N.u (.grid 0 D.R.m))⁻¹ * k * ch.S.N.u (.grid 0 D.R.m)).1 1).2⁻¹) y)) i (ys i)) =
      τ.sum fun d a' => a' * (∏ j, (d.1 j).fn (xs j)) * ∏ i, (d.2 i).fn (Function.update ys (FirstRowVertex.firstIx D) ((actO (ch.G.pS (.chi (FirstRowVertex.firstIx D) D.R.m : Pair T)) (ch.G.pT (.chi (FirstRowVertex.firstIx D) D.R.m : Pair T)) (ch.G.toPair (.chi (FirstRowVertex.firstIx D) D.R.m : Pair T) ((ch.S.N.u (.grid 0 D.R.m))⁻¹ * k * ch.S.N.u (.grid 0 D.R.m)).1 1).1⁻¹ (ch.G.toPair (.chi (FirstRowVertex.firstIx D) D.R.m : Pair T) ((ch.S.N.u (.grid 0 D.R.m))⁻¹ * k * ch.S.N.u (.grid 0 D.R.m)).1 1).2⁻¹) (ys (FirstRowVertex.firstIx D))) i) :=
    sum_update_comp τ (fun d j => (d.1 j).fn) (fun d i => (d.2 i).fn) (FirstRowVertex.firstIx D) (actO (ch.G.pS (.chi (FirstRowVertex.firstIx D) D.R.m : Pair T)) (ch.G.pT (.chi (FirstRowVertex.firstIx D) D.R.m : Pair T)) (ch.G.toPair (.chi (FirstRowVertex.firstIx D) D.R.m : Pair T) ((ch.S.N.u (.grid 0 D.R.m))⁻¹ * k * ch.S.N.u (.grid 0 D.R.m)).1 1).1⁻¹ (ch.G.toPair (.chi (FirstRowVertex.firstIx D) D.R.m : Pair T) ((ch.S.N.u (.grid 0 D.R.m))⁻¹ * k * ch.S.N.u (.grid 0 D.R.m)).1 1).2⁻¹) xs ys
  rw [hL]
  exact law_gen ch.S.toGridChoice (Set.mem_univ t) hτ k lam hlam _ hscal xs ys
end GlobalTheory.FirstRowTermLaw
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.leading_coefficient_term_law_theta : _root_.GlobalTheory.FunPr.ThetaLocalInputs → SumOKK → Big fun {D} {_Γ} _ _ {_Pl0} {T} {_A} {_Ks} _ _ _ {R} ch =>
    ∀ (t : T) a, ∀ β ∈ ch.S.supp t (ch.Phi a), ∀ τ, ch.S.IsExpansion t (ch.Phi a) β τ →
    ∀ (k : FinPt ch.G (.grid 0 D.R.m)), finG (ch.G.V (.grid 0 D.R.m)) k ∈ ch.S.levRow t 0 (Nat.zero_le _) →
    ∀ (hk : toXf k ∈ (levEnv D.sp.X' R.βX (R.datXt t)).J) (c : ℂ),
      ch.W.om (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) (ch.G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((ch.S.N.u (.grid 0 D.R.m))⁻¹ * k * ch.S.N.u (.grid 0 D.R.m)).1 1) (ch.S.Z.vac (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) = c • ch.S.Z.vac (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) →
    ∀ (xs : ∀ j : Fin D.R.m, WO (ch.G.pS (.top t j)) (ch.G.pT (.top t j)))
      (ys : ∀ i : Fin D.R.m, WO (ch.G.pS (.chi i D.R.m : Pair T)) (ch.G.pT (.chi i D.R.m : Pair T))),
      (((levEnv D.sp.X' R.βX (R.datXt t)).χ ⟨toXf k, hk⟩ : ℂˣ) : ℂ) * c *
        (τ.sum fun d a' => a' * (∏ j, (d.1 j).fn (xs j)) *
          ∏ i, Function.update (fun i => (d.2 i).fn) (GlobalTheory.FirstRowVertex.firstIx D)
            (fun y => (d.2 (GlobalTheory.FirstRowVertex.firstIx D)).fn (actO (ch.G.pS (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) (ch.G.pT (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) (ch.G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((ch.S.N.u (.grid 0 D.R.m))⁻¹ * k * ch.S.N.u (.grid 0 D.R.m)).1 1).1⁻¹ (ch.G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((ch.S.N.u (.grid 0 D.R.m))⁻¹ * k * ch.S.N.u (.grid 0 D.R.m)).1 1).2⁻¹ y)) i (ys i)) =
      τ.sum fun d a' => a' * (∏ j, (d.1 j).fn (xs j)) * ∏ i, (d.2 i).fn (ys i) := by
  first | exact @_root_.GlobalTheory.FirstRowTermLaw.lift_splits_locally | exact _root_.GlobalTheory.FirstRowTermLaw.lift_splits_locally | (intros; apply _root_.GlobalTheory.FirstRowTermLaw.lift_splits_locally <;> assumption)
end
