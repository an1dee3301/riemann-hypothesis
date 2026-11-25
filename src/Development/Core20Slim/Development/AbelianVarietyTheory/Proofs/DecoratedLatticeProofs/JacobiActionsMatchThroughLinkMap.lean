module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SkewGramHalfModule
public import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.StarPurelyImaginaryEqNeg
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompProjAnisotropicAnisotropicEmbedding
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselLineLinkGramSimilitudeBijective
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedBessel
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.Unf.LinkPoint

variable {D : D7}

theorem gram_zEll (T : HSp D) (ρ : ℕ) (z : Fin T.rank → D.host.E) :
    adj (zEll T ρ z) ⬝ (gA T ⬝ zEll T ρ z) =
      incA D (star z ⬝ᵥ T.gram *ᵥ z) • vecMulVec (fun i => cA D (ell D ρ i)) (ell D ρ) := by
  have h1 : adj (zEll T ρ z) = vecMulVec (fun i => cA D (ell D ρ i)) (ratV (star z)) := by
    funext i j
    change cA D (incA D (z j) * ell D ρ i) = cA D (ell D ρ i) * incA D (star (z j))
    rw [map_mul, GlobalTheory.DualPairCheck.cA_incA, mul_comm]
  have h2 : ratV (star z) ⬝ᵥ ratV (T.gram *ᵥ z) = incA D (star z ⬝ᵥ T.gram *ᵥ z) :=
    (RingHom.map_dotProduct (incA D) _ _).symm
  rw [h1, zEll, Matrix.mul_vecMulVec, gA, ← ratV_mulVec, Matrix.vecMulVec_mul_vecMulVec, h2, Matrix.vecMulVec_smul]

variable {W W₀ : HSp D} {ρ : ℕ} (d : HypDec W W₀ ρ)

theorem gA_jY : gA W ⬝ d.jY = adj d.pX := by rw [d.pX_eq, adj_mul, adj_adj, adj_gA]

theorem ptT_eq (L : HSp D) (y : Mx D L.rank ρ) (n : GA D W) :
    ptT d L y n = GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj L W₀ (y ⬝ (d.pX ⬝ (mt W n ⬝ d.j0))) := by
  rw [ptT, GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj, d.incAdj_apply, d.incY_apply, mt_inv, d.p0_eq]
  rw [adj_mul, adj_mul, adj_mul, ← gA_jY, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_smul]
  simp only [Matrix.mul_assoc]
  rw [gA_giA_cancel]

theorem trace_inverseGram_conj_smul_eq {R : Type} [CommRing R] {m k : ℕ} (s t : R) (G G' : Matrix (Fin m) (Fin m) R) (hG : G' * G = 1)
    (y : Matrix (Fin m) (Fin k) R) (y' : Matrix (Fin k) (Fin m) R) (M : Matrix (Fin k) (Fin k) R) :
    (G' * ((t • (G * y)) * (M * (s • (y' * G))))).trace = (((t * s) • (y' * (G * y))) * M).trace := by
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc G,
    ← Matrix.mul_assoc G', hG, Matrix.one_mul, Matrix.smul_mul, trace_smul, trace_smul, trace_mul_comm,
    Matrix.mul_assoc M, trace_mul_comm M, Matrix.mul_assoc y' G]

theorem hO_jY (L : HSp D) (n : GA D W) (η : Mx D ρ L.rank) : hO L W (d.jY ⬝ η) (mt W n⁻¹ ⬝ (d.jY ⬝ η)) =
    (giA L ⬝ (adj η ⬝ ((d.pX ⬝ (mt W n ⬝ d.jY)) ⬝ η))).trace := by
  rw [hO_eq_trace, mt_inv, d.pX_eq, adj_mul, adj_mul, adj_mul, adj_mul, adj_adj, adj_gA, adj_giA]
  simp only [Matrix.mul_assoc]
  rw [giA_gA_cancel]

theorem cenT_eq (L : HSp D) (y : Mx D L.rank ρ) (n : GA D W) :
    cenT d L y n = trHalf D ((incA D (D.host.xi0 * star D.host.xi0)⁻¹ •
      (adj y ⬝ (gA L ⬝ y)) ⬝ (d.pX ⬝ (mt W n ⬝ d.jY))).trace) := by
  have hs : cA D (incA D (-D.host.xi0⁻¹)) * incA D (-D.host.xi0⁻¹) = incA D (D.host.xi0 * star D.host.xi0)⁻¹ := by
    rw [GlobalTheory.DualPairCheck.cA_incA, ← map_mul, star_neg, star_inv₀, neg_mul_neg, _root_.mul_inv_rev]
  rw [cenT, symplOH_eq, d.incAdj_apply, d.incY_apply, hO_jY, ← hs, adj_smul, adj_mul, adj_adj, adj_gA]
  exact congrArg _ (trace_inverseGram_conj_smul_eq _ _ _ _ (giA_mul_gA L) _ _ _)

theorem neg_cenS_eq (T : HSp D) (x : Mx D T.rank ρ) (n : GA D W) :
    -cenS d T x n = trHalf D (((adj x ⬝ (gA T ⬝ x)) ⬝ (d.pX ⬝ (mt W n ⬝ d.jY))).trace) := by
  rw [cenS, ← symplOH_skew, symplOH_eq, hO_eq_trace, d.extX_apply, adj_mul, ← gA_jY, Matrix.mul_assoc, Matrix.mul_assoc,
    giA_gA_cancel, trace_mul_comm]
  simp only [Matrix.mul_assoc]

theorem link_point (D : D7) (ρ σ : ℕ) (B : BesLev D σ) (L' : HSp D) (ζ' : Fin L'.rank → D.host.E) (_ : IsLineVec L' ζ')
    (l : Link B L' ζ') (W W₀ : HSp D) (d : HypDec W W₀ ρ) (n : GA D W) (_ : n ∈ flagN d) :
    l.κ W₀ (ptS d L' (zEll L' ρ ζ') n) = ptT d B.L (yZero B.L ρ B.ζ) n ∧
      cenT d B.L (yZero B.L ρ B.ζ) n = -cenS d L' (zEll L' ρ ζ') n := by
  constructor
  · have h : (rat l.τ : Mx D B.L.rank L'.rank) ⬝ zEll L' ρ ζ' = yZero B.L ρ B.ζ := by
      have h0 : ratV (-B.ζ) = -ratV B.ζ := funext fun i => map_neg (incA D) _
      rw [yZero, zEll, zEll, Matrix.mul_vecMulVec, ← ratV_mulVec, l.map, h0, Matrix.neg_vecMulVec]
    rw [ptT_eq, Link.κ, ptS, d.extX_apply, ← h]
    simp only [Matrix.mul_assoc]
  · have hN : D.host.xi0 * star D.host.xi0 ≠ 0 :=
      mul_ne_zero (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D) (star_ne_zero.2 (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D))
    rw [cenT_eq, neg_cenS_eq, yZero, adj_neg, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_neg, neg_neg, gram_zEll, gram_zEll,
      smul_smul, ← map_mul, l.norm, inv_mul_cancel_left₀ hN]

end GlobalTheory.Unf.LinkPoint

end
