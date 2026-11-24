module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModerateGrowthOfHasCompactSupport
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBoundedUnitary
public import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
public import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Order.Lattice
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Order.OrderClosed
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

namespace GlobalTheory.Grow

open scoped TensorProduct NNReal ENNReal Topology
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.AdelicU
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Height

variable {D : D7} (V : HSp D)

theorem isCompact_setOf_height_le (C : ℝ) : IsCompact {g : GA D V | height V g ≤ C} := by
  refine (GlobalTheory.AdelicU.isCompact_height_le (F := D.host.F) D.sp.cm.sig V.gram C.toNNReal).of_isClosed_subset
    (isClosed_le (continuous_height V) continuous_const) fun g hg => ?_
  exact NNReal.le_toNNReal_of_coe_le hg

variable {X : Type} [NormedAddCommGroup X]

end Height

section Quot

variable {G : Type} [Group G] [MeasurableSpace G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [BorelSpace G] [LocallyCompactSpace G] [T2Space G] {R : Subgroup G} {μR : Measure R} {μG : Measure G} [SFinite μG]
  [μG.IsMulLeftInvariant] [μR.IsHaarMeasure] [μR.IsInvInvariant]

end Quot


end GlobalTheory.Grow
