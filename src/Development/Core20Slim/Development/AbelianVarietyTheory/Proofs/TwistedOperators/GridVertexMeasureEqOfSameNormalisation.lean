module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UpqLocallyCompactGroup
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsChainPols
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Definitions.Divisors.BplusOfEquivariant
public import Formalism.LocalRingCardinality.DataCD
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.MinfDensity
public import Formalism.LocalToGlobal.HermitianColumns.InLocalDiscriminantKernel
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.SatakeDualWeyl.Statement
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Classical
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Countable.Defs
public import Mathlib.Basic.ENNReal.Action
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.ENNReal.BigOperators
public import Mathlib.Basic.ENNReal.Operations
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Module
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Order
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.HaarNorm

theorem measLevW_unique {D : D7} (V : HSp D) (K : Subgroup (GL (Fin V.rank) (Lev.EAf D)))
    (good : ∀ ρ : D.what₂.Tau, Measure (UpqT (V.sig (tauE D ρ)).1 (V.sig (tauE D ρ)).2) → Prop)
    (hg : ∀ ρ m, good ρ m → m.IsHaarMeasure) {μ μ' : Measure (GA D V)}
    (h : Formalism.IndefR.Lev.IsMeasLevW V K good μ) (h' : Formalism.IndefR.Lev.IsMeasLevW V K good μ') : μ = μ' := by
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  obtain ⟨hμ, ⟨θ, hθ⟩, hθall⟩ := h
  obtain ⟨⟨A, hA⟩, hAall⟩ := hθall θ hθ
  obtain ⟨⟨m, hm⟩, hmall⟩ := hAall A hA
  have e := hmall m hm
  have e' := ((h'.2.2 θ hθ).2 A hA).2 m hm
  have hμ' := h'.1
  have hB : ∀ ρ : D.what₂.Tau, ∃ B : Set (UpqT (V.sig (tauE D ρ)).1 (V.sig (tauE D ρ)).2),
      MeasurableSet B ∧ m ρ B ≠ 0 ∧ m ρ B ≠ ⊤ := by
    intro ρ
    obtain ⟨j1, j2, j3, -, j5, -⟩ := GlobalTheory.UpqTopology.upq_lcsc (V.sig (tauE D ρ)).1 (V.sig (tauE D ρ)).2
    haveI := hg ρ (m ρ) (hm ρ)
    obtain ⟨C, hC, hC1⟩ := exists_compact_mem_nhds (1 : UpqT (V.sig (tauE D ρ)).1 (V.sig (tauE D ρ)).2)
    exact ⟨C, hC.measurableSet, (by first | exact (Measure.measure_pos_of_mem_nhds (m ρ) hC1).ne' | exact (measure_pos_of_nonempty_interior (m ρ) ⟨1, mem_interior_iff_mem_nhds.2 hC1⟩).ne'), hC.measure_lt_top.ne⟩
  choose B hBm hB0 hBt using hB
  set S := {h : GA D V | Lev.finE V h ∈ K ∧
      ∀ ρ, ∃ b ∈ B ρ, UpqT.mat b * A ρ = A ρ * infMat D.sp.cm.sig V.gram (θ ρ) h}
  have hS : μ S = ∏ ρ, m ρ (B ρ) := e B hBm
  have hS' : μ' S = ∏ ρ, m ρ (B ρ) := e' B hBm
  have hp0 : ∏ ρ, m ρ (B ρ) ≠ 0 := Finset.prod_ne_zero_iff.2 fun ρ _ => hB0 ρ
  have hpt : ∏ ρ, m ρ (B ρ) ≠ ⊤ := ENNReal.prod_ne_top fun ρ _ => hBt ρ
  have hc := Measure.isMulLeftInvariant_eq_smul μ' μ
  have hcS : μ' S = (Measure.haarScalarFactor μ' μ : ENNReal) * μ S := by
    conv_lhs => rw [hc]
    rfl
  rw [hS, hS'] at hcS
  have hc1 : (Measure.haarScalarFactor μ' μ : ENNReal) = 1 := by
    have := (ENNReal.mul_left_inj hp0 hpt).1 (hcS.symm.trans (one_mul _).symm)
    exact this
  rw [hc, ENNReal.coe_eq_one.1 hc1, one_smul]

theorem vol_nu_eq_of_isAt : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (M M' : Vol G) (X : Node) (K : Subgroup (GL (Fin (G.V X).rank) (Lev.EAf D))), M.IsAt X K → M'.IsAt X K → M.ν X = M'.ν X := by
  intro D T L sc G M M' X K h h'
  unfold GlobalTheory.FunObj.Vol.IsAt at h h'
  split_ifs at h h'
  · exact measLevW_unique _ _ _ (fun _ _ hm => hm.1) h.1 h'.1
  · exact measLevW_unique _ _ _ (fun _ _ hm => hm.1) h.1 h'.1

end GlobalTheory.HaarNorm
