module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalThetaSumRationalPairInvariant
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingInl
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ImportsBis
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDblCoordDblD
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaDiagInt
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRatPairIff
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRatVecIff
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFundDomainRationalPointsAdeleTupleFinitePo
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasurableThetaSumOfSchrodinger
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzSpaceTranslateMem
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParsevalFundamentalDomainTheta
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Core
public import Init.Data.Sum.Basic
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open MeasureTheory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.diagonalThetaSum_rationalPair_invariant : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ (κ : Type) [Fintype κ]
    (Φ : (κ ⊕ κ → AF F) → ℂ), ∀ γ ∈ GlobalTheory.WeilUnitaryTransport.ratPair F κ, ∀ w : (κ → AF F) × (κ → AF F),
      GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr ψ (Sum.elim (γ + w).1 (γ + w).1, Sum.elim (γ + w).2 (-(γ + w).2)) Φ) =
        GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr ψ (Sum.elim w.1 w.1, Sum.elim w.2 (-w.2)) Φ) := by
  first | exact @GlobalTheory.DiagThetaRatInv.diag_theta_rat_inv | exact GlobalTheory.DiagThetaRatInv.diag_theta_rat_inv | (intros; apply GlobalTheory.DiagThetaRatInv.diag_theta_rat_inv <;> assumption)
