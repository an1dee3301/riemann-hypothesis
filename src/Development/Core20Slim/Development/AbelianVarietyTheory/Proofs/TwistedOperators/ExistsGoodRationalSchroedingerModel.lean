module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalDarbouxHermitianTensorAdelesStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLatticeVacuumFinitePlacesRationalDarbouxStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIntegralPointsIndicatorIsVacuumStatement
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Classical
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
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
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Prod
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
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
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

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

namespace GlobalTheory.SquareAgree


open Classical in
theorem exists_good_model : ∀ (D : D7) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E), Bs.IsGood D.sp.cm.sig →
    ∀ {n d : ℕ} (V : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E n) (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E d) (r s r' s' : ℕ),
    V.IsHerm D.sp.cm.sig Bs r s → Ws.IsSkew D.sp.cm.sig Bs r' s' →
    ∀ (μ : Measure (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA D.sp.cm.sig V.J)) (dom : Set (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA D.sp.cm.sig V.J)),
      μ.IsHaarMeasure → IsFundamentalDomain (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ratU D.sp.cm.sig V.J) dom μ →
    ∃ M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig V Ws, M.μ = μ ∧ M.dom = dom ∧ M.IsGood Bs.ψ := by
  intro D Bs hB n d V Ws r s r' s' hV hW μ dom hμ hdom
  obtain ⟨co, hco⟩ := GlobalTheory.T.exists_rational_darboux_hermitian_tensor_adeles D.sp.cm.sig Bs V Ws r s r' s' hB hV hW
  let M0 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig V Ws := ⟨co, fun _ => 0, μ, dom⟩
  have hb := GlobalTheory.T.exists_latticeVacuum_finitePlaces_rationalDarboux D.sp.cm.sig Bs V Ws r s r' s' hB hV hW M0 hco
  have hc := GlobalTheory.T.eventually_integralPointsIndicator_isVacuum D.sp.cm.sig Bs V Ws r s r' s' hB hV hW M0 hco
  let ind : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := D.host.F), (Fin n × Fin d → Fv D.host.F v) → ℂ := fun v =>
    Set.indicator {x : Fin n × Fin d → Fv D.host.F v | ∀ k, x k ∈ v.adicCompletionIntegers D.host.F} 1
  refine ⟨⟨co, fun v => if M0.IsVac Bs.ψ v (ind v) then ind v else (hb v).choose, μ, dom⟩, rfl, rfl, ?_⟩
  refine ⟨hco, fun v => ?_, ?_, hμ, hdom⟩
  · change M0.IsVac Bs.ψ v (if M0.IsVac Bs.ψ v (ind v) then ind v else (hb v).choose)
    split_ifs with h
    · exact h
    · exact (hb v).choose_spec
  · filter_upwards [hc] with v hv
    change (if M0.IsVac Bs.ψ v (ind v) then ind v else (hb v).choose) = ind v
    exact if_pos hv

end GlobalTheory.SquareAgree
