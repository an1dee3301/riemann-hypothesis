module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormPeriodSq
public import Formalism.DoubleCosetMeasures.LowerUnipotentOrbits.RelIndexMulMeasure
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeasureToRealEqMass
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryEqRealMulFiniteSplit
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ClassFunctionSumIntegral
public import Formalism.LocalRingCardinality.DataCD
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.HermitianColumns.InLocalDiscriminantKernel
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.SatakeDualWeyl.Statement
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Countable.Defs
public import Mathlib.Basic.ENNReal.Action
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Logic.Basic
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.GroupTheory.Index
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Module
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Order
public import Mathlib.Topology.Separation.Hausdorff

@[expose] public section

open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LevelIndexMeasure

theorem measure_eq_relIndex_smul : ∀ {D : D7} (V : HSp D) (n : ℕ) (ι : Formalism.MainNotions.StandardLatticesGL3.GA D n →* GA D V) (J J₀ : Subgroup (Formalism.MainNotions.StandardLatticesGL3.GA D n))
  (K K₀ : Subgroup (GL (Fin V.rank) (Lev.EAf D))) (μ μ₀ : Measure (GA D V)), ι.range = GfC V → J ≤ J₀ → J.relIndex J₀ ≠ 0 →
  IsOpenCompactLevel V K → IsOpenCompactLevel V K₀ → (∀ x, Lev.finE V (ι x) ∈ K ↔ x ∈ J) → (∀ x, Lev.finE V (ι x) ∈ K₀ ↔ x ∈ J₀) →
  Lev.IsMeasLevDef V K μ → Lev.IsMeasLevDef V K₀ μ₀ → μ = (J.relIndex J₀ : ENNReal) • μ₀ := by
  intro D V n ι J J₀ K K₀ μ μ₀ hι hJ hJi hK hK₀ hJK hJK₀ hμ hμ₀
  obtain ⟨hLC, hSC, hT2, hB, hTG, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  haveI := hLC; haveI := hSC; haveI := hT2; haveI := hB; haveI := hTG
  haveI : μ.IsHaarMeasure := hμ.1
  haveI : μ₀.IsHaarMeasure := hμ₀.1

  have hfin : ∀ g : GA D V, ∃ x, Lev.finE V (ι x) = Lev.finE V g := by
    intro g
    obtain ⟨k, k1, k2⟩ := GlobalTheory.UnitarySplit.ga_glue V 1 _ (one_mem _) (GlobalTheory.UnitarySplit.finHom_mem V g)
    have hk : k ∈ ι.range := by
      rw [hι]
      exact MonoidHom.mem_ker.2 k1
    obtain ⟨x, rfl⟩ := hk
    refine ⟨x, ?_⟩
    show Formalism.UG.bc (Lev.swapAE D) (finHom V (ι x)) = Formalism.UG.bc (Lev.swapAE D) (finHom V g)
    rw [k2]
  have hHH : K.comap (Lev.finE V) ≤ K₀.comap (Lev.finE V) := by
    intro g hg
    obtain ⟨x, hx⟩ := hfin g
    change Lev.finE V g ∈ K at hg
    show Lev.finE V g ∈ K₀
    rw [← hx] at hg ⊢
    exact (hJK₀ x).2 (hJ ((hJK x).1 hg))
  have e1 : J = K.comap ((Lev.finE V).comp ι) := by
    ext x
    exact (hJK x).symm
  have e2 : (J₀.map ι).map (Lev.finE V) = (K₀.comap (Lev.finE V)).map (Lev.finE V) := by
    ext y
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨ι x, (hJK₀ x).2 hx, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      obtain ⟨x, hx⟩ := hfin g
      refine ⟨ι x, ⟨x, (hJK₀ x).1 ?_, rfl⟩, hx⟩
      rw [hx]
      exact hg
  have hidx : (K.comap (Lev.finE V)).relIndex (K₀.comap (Lev.finE V)) = J.relIndex J₀ := by
    rw [e1, Subgroup.relIndex_comap, Subgroup.relIndex_comap, ← Subgroup.map_map, e2]
  haveI : ((K.comap (Lev.finE V)).subgroupOf (K₀.comap (Lev.finE V))).FiniteIndex := ⟨hidx.trans_ne hJi⟩
  have hm := Formalism.DoubleCosetMeasures.P.GLRed.relIndex_mul_measure _ _ hHH hK.1.measurableSet μ
  rw [hidx, GlobalTheory.Mass.Levels.measure_comap_finE hμ, mul_one] at hm
  have h0 : μ₀ (K₀.comap (Lev.finE V)) = 1 := GlobalTheory.Mass.Levels.measure_comap_finE hμ₀
  have heq := Measure.isMulLeftInvariant_eq_smul μ μ₀
  have hc : ((Measure.haarScalarFactor μ μ₀ : NNReal) : ENNReal) = (J.relIndex J₀ : ENNReal) := by
    have := congrArg (fun m : Measure (GA D V) => m ((K₀.comap (Lev.finE V) : Subgroup (GA D V)) : Set (GA D V))) heq
    simp only [Measure.smul_apply, h0, ← hm] at this
    rw [this, ENNReal.smul_def, smul_eq_mul, mul_one]
  ext s hs
  rw [heq, Measure.smul_apply, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, smul_eq_mul, hc]

end GlobalTheory.LevelIndexMeasure
