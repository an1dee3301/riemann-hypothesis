module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompactElementGaussianList
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaSubSelf
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HypothesesAbsDet
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsArchEquivEq
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.AdelicUnitaryRealPointsStructureRealPlaces
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedSmooth
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.AtTauExUniqueHolds
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.InfFam
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Classical
public import Init.Core
public import Init.Data.List.Basic
public import Init.Data.List.Lemmas
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Dedup
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open scoped ComplexConjugate
noncomputable section
namespace GlobalTheory.KInfLines
variable {D : D7}
end GlobalTheory.KInfLines
namespace GlobalTheory.KInfLines
variable {D : D7}
end GlobalTheory.KInfLines
namespace GlobalTheory.KInfLines
variable {D : D7} {W : HSp D} {V : IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E W.rank}
end GlobalTheory.KInfLines
namespace GlobalTheory.KInfLines
variable {D : D7} {W : HSp D} {V : IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E W.rank}
theorem kInfinity_prod_lines : FunPr.ThetaLocalInputs → ∀ (D : D7) (θ : InfFam D) (W : HSp D) (Bs : IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E)
    (V : IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E W.rank) (r s : ℕ) (hJ : V.J = (1 : D.host.E) • W.gram),
    IsInfFam θ → Bs.IsGood D.sp.cm.sig → V.IsHerm D.sp.cm.sig Bs r s →
    ∀ k ∈ IndefiniteRowSideFullHecke.WeilTensorModels.KInf D.sp.cm.sig V Bs.emb,
    ∃ l : List (D.what₂.Tau × Matrix (Fin W.rank) (Fin W.rank) ℂ),
      (∀ q ∈ l, q.2 ∈ lieAt W q.1 ∧ ∀ t : ℝ,
        IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W 1 hJ (oneP θ W q.1 q.2 t) ∈ IndefiniteRowSideFullHecke.WeilTensorModels.KInf D.sp.cm.sig V Bs.emb) ∧
      k = (l.map fun q => IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W 1 hJ (oneP θ W q.1 q.2 1)).prod := by
  intro _ D θ W Bs V r s hJ hθ _ hV k hk
  obtain rfl := Eqv.eq_thetaC D hθ
  choose C hC using cartan_data hJ Bs hV hk
  choose Z hZ using fun t => exists_log_of_cartan (SmoothForms.RealPts.gramAt_herm W t) (hC t).1
    (unitFam_gsOf hJ k t) (hC t).2.1
  refine ⟨Finset.univ.toList.map fun t => (t, Z t), ?_, prod_eq hJ hk.1 Z fun t => ⟨(hZ t).1, (hZ t).2.2⟩⟩
  intro q hq
  obtain ⟨t, -, rfl⟩ := List.mem_map.1 hq
  exact ⟨(hZ t).1, line_mem hJ Bs C (fun t => (hC t).2.2) (hZ t).1 (hZ t).2.1⟩
end GlobalTheory.KInfLines
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kInfinity_action_prod_lines : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (θ : InfFam D) (W : HSp D) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E)
    (V : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E W.rank) (r s : ℕ) (hJ : V.J = (1 : D.host.E) • W.gram),
    IsInfFam θ → Bs.IsGood D.sp.cm.sig → V.IsHerm D.sp.cm.sig Bs r s →
    ∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf D.sp.cm.sig V Bs.emb,
    ∃ l : List (D.what₂.Tau × Matrix (Fin W.rank) (Fin W.rank) ℂ),
      (∀ q ∈ l, q.2 ∈ lieAt W q.1 ∧ ∀ t : ℝ,
        GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W 1 hJ (oneP θ W q.1 q.2 t) ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf D.sp.cm.sig V Bs.emb) ∧
      k = (l.map fun q => GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W 1 hJ (oneP θ W q.1 q.2 1)).prod := by
  first | exact @_root_.GlobalTheory.KInfLines.kInfinity_prod_lines | exact _root_.GlobalTheory.KInfLines.kInfinity_prod_lines | (intros; apply _root_.GlobalTheory.KInfLines.kInfinity_prod_lines <;> assumption)
end
