module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTowerStageFiniteFactor
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
public import Development.Core20Slim.Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ExistsFinitePlaceThetaMatch
public import Development.Core20Slim.Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.StageUniqueOfArchimedeanTriple
public import Mathlib
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegIdxOfIsStd
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitCharTriangle
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Definitions.Divisors.LeastSplitAuxiliaryPrimeThetaChainSpec
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Function
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Basic
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Hom.Instances
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Torsion.Free
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.NoZeroSMulDivisors.Basic
public import Mathlib.Algebra.NoZeroSMulDivisors.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct
namespace GlobalTheory.StageFinMatch
end GlobalTheory.StageFinMatch
namespace GlobalTheory.StageFinMatch
theorem theta_bottom_finite_match : FunPr.ThetaLocalInputs → IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    GBig fun {D} {T} {Lc} {sc} G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m) (p q : ℕ) (A A' WW : HSp D)
    (X : Tri T A A' WW), SqTower.IsStageC W i j p q X →
    ∀ (FA : ChainFr.Fr A) (FA' : ChainFr.Fr A') (FW : ChainFr.Fr WW) (t : T),
    SquareComm.IsFinF W.ψ W.θ true FA FW (X.f t) → SquareComm.IsFinF W.ψ W.θ false FA' FW (X.f' t) →
    ∀ (Pi : ModuleCat.{0} ℂ) rf rl p p', SquareComm.IsMatch W.ψ W.θ FA FA' FW (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2))
      (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2)) (X.ω t) (X.ω' t) Pi rf rl p p' →
    ∀ (Pr Pf : ModuleCat.{0} ℂ) (q : PolF D WW.rank A.rank →ₗ[ℂ] Pr) (q' : PolF D WW.rank A'.rank →ₗ[ℂ] Pr)
      (r : (WO A WW → ℂ) →ₗ[ℂ] Pf) (r' : (WO A' WW → ℂ) →ₗ[ℂ] Pf) (e : Pr ⊗[ℂ] Pf ≃ₗ[ℂ] Pi),
      Function.Surjective q → Function.Surjective q' →
      (∀ f, SquareComm.IsFinF W.ψ W.θ true FA FW f → ∀ P, p (SquareComm.fockF W.ψ W.θ true FA FW f P) = e (q P ⊗ₜ r f)) →
      (∀ f, SquareComm.IsFinF W.ψ W.θ false FA' FW f → ∀ P, p' (SquareComm.fockF W.ψ W.θ false FA' FW f P) = e (q' P ⊗ₜ r' f)) →
      ∃ κ : ℂ, κ ≠ 0 ∧ r (X.f t) = κ • r' (X.f' t) := by
  intro hP hK hL
  refine gBig_two' (_root_.GlobalTheory.T.finite_place_theta_matching hP hK hL) (_root_.GlobalTheory.T.theta_stage_unique hP hK hL) fun {D T Lc sc} G μ₀ C x b₀ hA hB => ?_
  intro W i j a b A A' WW X hX FA FA' FW t hf hf' Pi rf rl p p' hm Pr Pf q q' r r' e hq hq' hp hp'
  obtain ⟨Pi₀, rf₀, rl₀, p₀, p₀', hm₀, P, P', κ, hne, heq⟩ := hA W i j a b A A' WW X hX FA FA' FW t hf hf'
  obtain ⟨E, c, hc, hE, hE'⟩ := hB W i j a b A A' WW X hX FA FA' FW t Pi₀ rf₀ rl₀ p₀ p₀' Pi rf rl p p' hm₀ hm
  have m1 : SquareComm.fockF W.ψ W.θ true FA FW (X.f t) P ∈ SquareComm.algF W.ψ W.θ true FA FW :=
    Submodule.subset_span ⟨_, P, hf, rfl⟩
  have m2 : SquareComm.fockF W.ψ W.θ false FA' FW (X.f' t) P' ∈ SquareComm.algF W.ψ W.θ false FA' FW :=
    Submodule.subset_span ⟨_, P', hf', rfl⟩
  have k : p (SquareComm.fockF W.ψ W.θ true FA FW (X.f t) P) =
      (c * κ) • p' (SquareComm.fockF W.ψ W.θ false FA' FW (X.f' t) P') := by
    rw [hE _ m1, hE' _ m2, heq, LinearEquiv.map_smul, smul_smul]
  have kne : p (SquareComm.fockF W.ψ W.θ true FA FW (X.f t) P) ≠ 0 := by
    rw [hE _ m1]
    exact smul_ne_zero hc ((LinearEquiv.map_ne_zero_iff E).mpr hne)
  rw [hp _ hf P, hp' _ hf' P', ← LinearEquiv.map_smul, TensorProduct.smul_tmul'] at k
  rw [hp _ hf P] at kne
  have kne' : q P ⊗ₜ[ℂ] r (X.f t) ≠ 0 := fun h0 => kne (by rw [h0, map_zero])
  exact tmul_right_prop (e.injective k) kne'
end GlobalTheory.StageFinMatch
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_finiteData_match_each_stage : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    GBig fun {D} {T} {Lc} {sc} G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m) (p q : ℕ) (A A' WW : HSp D)
    (X : Tri T A A' WW), GlobalTheory.SqTower.IsStageC W i j p q X →
    ∀ (FA : GlobalTheory.ChainFr.Fr A) (FA' : GlobalTheory.ChainFr.Fr A') (FW : GlobalTheory.ChainFr.Fr WW) (t : T),
    GlobalTheory.SquareComm.IsFinF W.ψ W.θ true FA FW (X.f t) → GlobalTheory.SquareComm.IsFinF W.ψ W.θ false FA' FW (X.f' t) →
    ∀ (Pi : ModuleCat.{0} ℂ) rf rl p p', GlobalTheory.SquareComm.IsMatch W.ψ W.θ FA FA' FW (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2))
      (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2)) (X.ω t) (X.ω' t) Pi rf rl p p' →
    ∀ (Pr Pf : ModuleCat.{0} ℂ) (q : PolF D WW.rank A.rank →ₗ[ℂ] Pr) (q' : PolF D WW.rank A'.rank →ₗ[ℂ] Pr)
      (r : (WO A WW → ℂ) →ₗ[ℂ] Pf) (r' : (WO A' WW → ℂ) →ₗ[ℂ] Pf) (e : Pr ⊗[ℂ] Pf ≃ₗ[ℂ] Pi),
      Function.Surjective q → Function.Surjective q' →
      (∀ f, GlobalTheory.SquareComm.IsFinF W.ψ W.θ true FA FW f → ∀ P, p (GlobalTheory.SquareComm.fockF W.ψ W.θ true FA FW f P) = e (q P ⊗ₜ r f)) →
      (∀ f, GlobalTheory.SquareComm.IsFinF W.ψ W.θ false FA' FW f → ∀ P, p' (GlobalTheory.SquareComm.fockF W.ψ W.θ false FA' FW f P) = e (q' P ⊗ₜ r' f)) →
      ∃ κ : ℂ, κ ≠ 0 ∧ r (X.f t) = κ • r' (X.f' t) := by
  first | exact @_root_.GlobalTheory.StageFinMatch.theta_bottom_finite_match | exact _root_.GlobalTheory.StageFinMatch.theta_bottom_finite_match | (intros; apply _root_.GlobalTheory.StageFinMatch.theta_bottom_finite_match <;> assumption)
end
