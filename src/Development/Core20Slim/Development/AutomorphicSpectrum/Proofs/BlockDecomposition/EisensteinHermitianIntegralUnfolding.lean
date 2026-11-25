module

public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ColJoinColLColR
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
public import Development.Core20Slim.Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.EisCellsDefs
public import Development.Core20Slim.Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.ThetaOrbits
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Fin.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Regular
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.MeasureTheory.OuterMeasure.AE
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Filter.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.Compactness.Paracompact
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Metrizable.Basic
public import Mathlib.Topology.Metrizable.Urysohn
public import Mathlib.Topology.Order
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.Separation.Regular

@[expose] public section

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.CompanionTheory.EisUnfold
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.EisUnfold.NegStep

theorem integral_neg_of_secondCountable {G E : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (μ : Measure G) [μ.IsAddHaarMeasure] (f : G → E) :
    ∫ x, f (-x) ∂μ = ∫ x, f x ∂μ := by
  have : μ.IsNegInvariant := Measure.IsAddHaarMeasure.isNegInvariant_of_regular μ
  exact integral_neg_eq_self f μ

theorem colJoin_zero_mul {R : Type*} [NonUnitalNonAssocSemiring R] {m r s : ℕ} (p : Matrix (Fin m) (Fin r) R)
    (a : Matrix (Fin (r + s)) (Fin (r + s)) R) (c : Matrix (Fin r) (Fin (r + s)) R)
    (h : ∀ j : Fin r, a (Fin.castAdd s j) = c j) :
    colJoin p (0 : Matrix (Fin m) (Fin s) R) * a = p * c := by
  ext i k
  simp [Matrix.mul_apply, Fin.sum_univ_add, h]

theorem inner_neg_neg {D : D7} (V : HSp D) {n : ℕ} (t : Mx D V.rank n) : inner V (-t) (-t) = inner V t t := by
  unfold GlobalTheory.StdUnn.inner
  rw [adj_neg]
  simp only [Matrix.neg_mul, Matrix.mul_neg, neg_neg]

theorem integral_colJoin_neg_eq_J : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V : HSp D) (r s : ℕ) (μr : Measure (Mx D V.rank r))
    (𝓕r : Set (Mx D V.rank r)), IsCovolOne (ratMx D V.rank r) μr 𝓕r →
    ∀ (c : Matrix (Fin r) (Fin (r + s)) D.host.E) (a : Matrix (Fin (r + s)) (Fin (r + s)) D.host.E), IsCompl c a →
    ∀ (b : HermE D r) (Φ : Mx D V.rank (r + s) → ℂ),
      ∫ t, ψ (halfTr (Matrix.trace (HMul.hMul (rat b.1) (inner V t t) : Mx D r r))) *
          Φ (HMul.hMul (colJoin (-t) (0 : Mx D V.rank s)) (rat a)) ∂μr = J ψ V μr (pull c Φ) b := by
  intro D ψ V r s μr 𝓕r hcov c a hca b Φ
  obtain ⟨h1, h2, h3, h4, -⟩ := lattice_Mx D V.rank r
  have hB : BorelSpace (Mx D V.rank r) := ⟨rfl⟩
  have hH : μr.IsAddHaarMeasure := hcov.1
  have hrow : ∀ j : Fin r, rat a (Fin.castAdd s j) = rat c j := by
    intro j
    have := hca.2 (Fin.castAdd s j) j.isLt
    funext k
    show incA D (a (Fin.castAdd s j) k) = incA D (c j k)
    rw [this]
    rfl
  have key : ∀ t : Mx D V.rank r,
      ψ (halfTr (Matrix.trace (HMul.hMul (rat b.1) (inner V t t) : Mx D r r))) *
          Φ (HMul.hMul (colJoin (-t) (0 : Mx D V.rank s)) (rat a)) =
      (fun y : Mx D V.rank r => pull c Φ y * ψ (halfTr (Matrix.trace (HMul.hMul (rat b.1) (inner V y y) : Mx D r r)))) (-t) := by
    intro t
    have e : (HMul.hMul (colJoin (-t) (0 : Mx D V.rank s)) (rat a) : Mx D V.rank (r + s)) = HMul.hMul (-t) (rat c) :=
      colJoin_zero_mul (-t) (rat a) (rat c) hrow
    show _ = Φ (HMul.hMul (-t) (rat c)) * _
    rw [e, inner_neg_neg, mul_comm]
  exact (integral_congr_ae (Filter.Eventually.of_forall key)).trans
    (integral_neg_of_secondCountable (E := ℂ) μr
      (fun y : Mx D V.rank r => pull c Φ y * ψ (halfTr (Matrix.trace (HMul.hMul (rat b.1) (inner V y y) : Mx D r r)))))

end GlobalTheory.CompanionTheory.EisUnfold.NegStep
