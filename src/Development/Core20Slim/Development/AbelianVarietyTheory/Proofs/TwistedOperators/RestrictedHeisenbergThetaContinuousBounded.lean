module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfLintegralEqZero
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
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
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.MeasureTheory.OuterMeasure.AE
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.Basic
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.EMetricSpace.Defs
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Metrizable.Uniformity
public import Mathlib.Topology.Order
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix

namespace GlobalTheory.IndefiniteRowSideFullHecke.ResCont

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem continuous_bounded_setIntegral {X Y : Type} [TopologicalSpace X] [FirstCountableTopology X] [TopologicalSpace Y]
    [MeasurableSpace Y] [OpensMeasurableSpace Y] (μ : Measure Y) (s : Set Y) (hs : μ s < ⊤) (F : X → Y → ℂ)
    (hc : Continuous fun q : X × Y => F q.1 q.2) (K : ℝ) (hb : ∀ x y, ‖F x y‖ ≤ K) :
    Continuous (fun x => ∫ y in s, F x y ∂μ) ∧ ∀ x, ‖∫ y in s, F x y ∂μ‖ ≤ K * (μ.restrict s).real Set.univ := by
  haveI : IsFiniteMeasure (μ.restrict s) := isFiniteMeasure_restrict.2 hs.ne
  refine ⟨?_, fun x => norm_integral_le_of_norm_le_const (.of_forall fun y => hb x y)⟩
  refine continuous_of_dominated (bound := fun _ => K) (fun x => ?_) (fun x => .of_forall fun y => hb x y)
    (integrable_const K) (.of_forall fun y => ?_)
  · exact (hc.comp (continuous_const.prodMk continuous_id) : Continuous fun y => F x y).aestronglyMeasurable
  · exact (hc.comp (continuous_id.prodMk continuous_const) : Continuous fun x => F x y)

theorem res_heisO_continuous_bounded : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C C' : Matrix (Fin V.rank) (Fin r) D.host.E)
    (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.ratMx D W.rank r) μ 𝓨 →
    ∀ f, IsThetaFunO ψ V W f →
    Continuous (fun p : WO V' W × Mx D W.rank r =>
      GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 (heisO ψ V W (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C' p.2) f) p.1) ∧
    ∃ M : ℝ, ∀ x u, ‖GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 (heisO ψ V W (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C' u) f) x‖ ≤ M := by
  intro D V V' W r C C' B ψ hψ μ 𝓨 h𝓨 f hf
  obtain ⟨K, hK⟩ := GlobalTheory.OrientedHeis.theta_bounded hψ hf
  have hn : ∀ z, ‖ψ z‖ = 1 := hψ.1.2.1
  have hfin : μ 𝓨 < ⊤ := by rw [h𝓨.2.2]; exact ENNReal.one_lt_top
  haveI : IsFiniteMeasure (μ.restrict 𝓨) := isFiniteMeasure_restrict.2 hfin.ne
  obtain ⟨-, -, i3, -⟩ := GlobalTheory.MixModel.lattice_Mx D W.rank r
  obtain ⟨-, -, j3, -⟩ := GlobalTheory.MixModel.lattice_Mx D W.rank V'.rank
  haveI : BorelSpace (Mx D W.rank r) := ⟨rfl⟩
  haveI : OpensMeasurableSpace (Mx D W.rank r) := BorelSpace.opensMeasurable
  haveI : SecondCountableTopology (WO V' W × Mx D W.rank r) := @TopologicalSpace.instSecondCountableTopologyProd _ _ _ _ j3 i3
  haveI : FirstCountableTopology (WO V' W × Mx D W.rank r) :=
    TopologicalSpace.SecondCountableTopology.to_firstCountableTopology _
  have hiso : ∀ (C₀ : Matrix (Fin V.rank) (Fin r) D.host.E),
      Continuous (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C₀) := fun C₀ =>
    Continuous.matrix_mul continuous_id continuous_const
  have hmid : Continuous (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.midPart V V' W B) :=
    Continuous.matrix_mul continuous_id continuous_const
  have hFb : ∀ (p : WO V' W × Mx D W.rank r) (y : Mx D W.rank r),
      ‖heisO ψ V W (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C' p.2) f
        (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C y + GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.midPart V V' W B p.1)‖ ≤ K := fun p y => by
    simp only [heisO, norm_mul, hn, one_mul]
    exact hK _
  have ha : Continuous fun q : (WO V' W × Mx D W.rank r) × Mx D W.rank r =>
      GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C q.2 + GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.midPart V V' W B q.1.1 :=
    ((hiso C).comp continuous_snd).add (hmid.comp (continuous_fst.comp continuous_fst))
  have hb : Continuous fun q : (WO V' W × Mx D W.rank r) × Mx D W.rank r =>
      GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C' q.1.2 := (hiso C').comp (continuous_snd.comp continuous_fst)
  have hFc : Continuous fun q : (WO V' W × Mx D W.rank r) × Mx D W.rank r =>
      heisO ψ V W (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C' q.1.2) f
        (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C q.2 + GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.midPart V V' W B q.1.1) :=
    (hψ.1.1.comp (GlobalTheory.OrientedHeis.continuous_symplOH ha hb)).mul (hf.cont.comp (ha.add hb))
  have h := continuous_bounded_setIntegral μ 𝓨 hfin _ hFc K hFb
  exact ⟨h.1, _, fun x u => h.2 (x, u)⟩

end GlobalTheory.IndefiniteRowSideFullHecke.ResCont

end
