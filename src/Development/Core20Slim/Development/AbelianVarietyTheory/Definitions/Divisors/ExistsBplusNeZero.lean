module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.BplusOfEquivariant
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.QuotVolumeNeZeroNeTop
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousAdelicUnitaryEmbedding
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BesselCharacterGenericCharacterLaws
public import Formalism.LocalRingCardinality.SpanPowerMembership.ExistsOmegaLeb
public import Formalism.LocalRingCardinality.SpanPowerMembership.HaarDensityNeZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
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
public import Init.Data.Cast
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
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
public import Mathlib.Data.Nat.Cast.Defs
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
public import Mathlib.MeasureTheory.OuterMeasure.Basic
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
public import Mathlib.Topology.Closure
public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Neighborhoods
public import Mathlib.Topology.Order
public import Mathlib.Topology.Separation.Hausdorff

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj

namespace GlobalTheory.FunObjModel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem isMeasLevW_unique {V : HSp D} {K : Subgroup (GL (Fin V.rank) (Lev.EAf D))} {good} {μ μ' : Measure (GA D V)}
    (hg : ∀ ρ m, good ρ m → m.IsHaarMeasure) (h : Lev.IsMeasLevW V K good μ) (h' : Lev.IsMeasLevW V K good μ') : μ = μ' := by
  obtain ⟨hloc, hsc, ht2, hbor, htg, -, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  obtain ⟨hμ, ⟨θ, hθ⟩, hall⟩ := h
  obtain ⟨hμ', -, hall'⟩ := h'
  obtain ⟨⟨A, hA⟩, hallA⟩ := hall θ hθ
  obtain ⟨⟨m, hm⟩, hallm⟩ := hallA A hA
  have hvol := hallm m hm
  have hvol' := (hall' θ hθ).2 A hA |>.2 m hm

  choose C hC hC1 using fun ρ => exists_compact_mem_nhds (1 : Formalism.BasicNotions.UpqT (V.sig (tauE D ρ)).1 (V.sig (tauE D ρ)).2)
  have hB : ∀ ρ, MeasurableSet (interior (C ρ)) := fun ρ => isOpen_interior.measurableSet
  have hpos : ∀ ρ, m ρ (interior (C ρ)) ≠ 0 := fun ρ => by
    have := hg ρ (m ρ) (hm ρ)
    exact isOpen_interior.measure_ne_zero (m ρ) ⟨1, mem_interior_iff_mem_nhds.2 (hC1 ρ)⟩
  have hfin : ∀ ρ, m ρ (interior (C ρ)) ≠ ⊤ := fun ρ => by
    have := hg ρ (m ρ) (hm ρ)
    exact ((measure_mono interior_subset).trans_lt (hC ρ).measure_lt_top).ne
  have e1 := hvol (fun ρ => interior (C ρ)) hB
  have e2 := hvol' (fun ρ => interior (C ρ)) hB
  set P := ∏ ρ, m ρ (interior (C ρ)) with hPdef
  have hP0 : P ≠ 0 := Finset.prod_ne_zero_iff.2 fun ρ _ => hpos ρ
  have hPtop : P ≠ ⊤ := ENNReal.prod_ne_top fun ρ _ => hfin ρ
  have := hμ
  have := hμ'

  obtain ⟨c, hs⟩ : ∃ c : NNReal, μ' = c • μ := ⟨_, MeasureTheory.Measure.isMulLeftInvariant_eq_smul μ' μ⟩
  have e3 : ∀ s, μ' s = c * μ s := fun s => by
    simp only [hs, MeasureTheory.Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
  rw [e3, e1] at e2
  have hc1 : c = 1 := by exact_mod_cast (ENNReal.mul_eq_right hP0 hPtop).1 e2
  rw [hs, hc1, one_smul]

theorem isAt_unique {M M' : Vol G} {X : Node} {K} (h : M.IsAt X K) (h' : M'.IsAt X K) : M.ν X = M'.ν X := by
  unfold Vol.IsAt at h h'
  split_ifs at h h'
  · exact isMeasLevW_unique (fun _ _ hm => hm.1) h.1 h'.1
  · exact isMeasLevW_unique (fun _ _ hm => hm.1) h.1 h'.1

variable (W : G.Weil)

end GlobalTheory.FunObjModel

end
