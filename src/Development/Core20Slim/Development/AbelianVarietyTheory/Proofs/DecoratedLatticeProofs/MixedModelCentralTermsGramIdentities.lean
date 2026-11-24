module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SkewGramHalfModule
public import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.StarPurelyImaginaryEqNeg
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ContinuousResTSymm
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompProjAnisotropicAnisotropicEmbedding
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittHyperbolicAnisotropicCommuteLevi
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
public import Formalism.LocalRingCardinality.DataHost
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
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Trace.Defs

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CentralGram

theorem mul_trace_neg {R : Type} [CommRing R] {n : ℕ} (a : R) (c H : Matrix (Fin n) (Fin n) R) :
    a * ((-c) * H).trace = -((a • H) * c).trace := by
  rw [Matrix.neg_mul, trace_neg, trace_mul_comm, Matrix.smul_mul, trace_smul, smul_eq_mul, mul_neg]

theorem trace_cycle_smul {R : Type} [CommRing R] {m n : ℕ} (a : R) (c : Matrix (Fin n) (Fin n) R)
    (y : Matrix (Fin m) (Fin n) R) (z : Matrix (Fin n) (Fin m) R) (G : Matrix (Fin m) (Fin m) R) :
    (y * (a • (c * (z * G)))).trace = ((a • (z * (G * y))) * c).trace := by
  rw [Matrix.mul_smul, Matrix.smul_mul, trace_smul, trace_smul, ← Matrix.mul_assoc y, trace_mul_comm]
  simp only [Matrix.mul_assoc]

theorem move_sub {R : Type} [CommRing R] {m n k : ℕ} {M : Matrix (Fin m) (Fin m) R} {X Y : Matrix (Fin m) (Fin n) R}
    {c : Matrix (Fin n) (Fin n) R} (h : M * Y = Y + X * (-c)) (a : R) (z : Matrix (Fin n) (Fin k) R) :
    M * (Y * ((-a) • z)) - Y * ((-a) • z) = X * (a • (c * z)) := by
  rw [← Matrix.mul_assoc, h, Matrix.add_mul, add_sub_cancel_left, Matrix.mul_assoc, neg_smul, Matrix.neg_mul,
    Matrix.mul_neg c, neg_neg, Matrix.mul_smul c]

variable {D : D7}

theorem gramSkew_map (T : HSp D) {ρ : ℕ} (x : Mx D T.rank ρ) :
    (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.gramSkew T x).map (cA D) = incA D D.host.xi0 • (adj x * (gA T * x)) := by
  have h : adj (adj x * (gA T * x)) = adj x * (gA T * x) := gram_swap T rfl |>.symm
  have h2 : cA D (-incA D D.host.xi0) = incA D D.host.xi0 := by
    rw [map_neg, GlobalTheory.DualPairCheck.cA_incA, GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg, map_neg, neg_neg]
  funext i j
  have h3 := congrFun (congrFun h i) j
  change cA D ((-incA D D.host.xi0) * (adj x * (gA T * x)) j i) = incA D D.host.xi0 * (adj x * (gA T * x)) i j
  rw [map_mul, h2, ← h3]
  rfl

theorem starAdj_extX_mul {S S₀ : HSp D} (T : HSp D) {ρ : ℕ} (d : HypDec S S₀ ρ) (x : Mx D T.rank ρ) :
    GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.starAdj S T (d.extX T x) * x = d.jY * (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.gramSkew T x).map (cA D) := by
  rw [gramSkew_map, GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.starAdj, HypDec.extX_apply, d.pX_eq]
  simp only [adj_mul, adj_adj, adj_gA, Matrix.mul_assoc, giA_gA_cancel, Matrix.smul_mul, Matrix.mul_smul]

theorem qS_eq {S S₀ : HSp D} (T : HSp D) {ρ : ℕ} (d : HypDec S S₀ ρ) (c : skewA D ρ) (x : Mx D T.rank ρ) :
    d.qS T c x = -(algebraMap D.host.F (AF D.host.F) (1 / 2) *
      Algebra.trace (AF D.host.F) (AE D) ((GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.gramSkew T x).map (cA D) * c.1).trace) := by
  have hc : adj c.1 = -c.1 := c.2
  have h : incA D D.host.xi0 * pairS T x (x * c.1) =
      -((GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.gramSkew T x).map (cA D) * c.1).trace := by
    rw [gramSkew_map, pairS, adj_mul, hc, Matrix.mul_assoc]
    exact mul_trace_neg _ _ _
  refine (d.symplOH_extX_extY T x _).trans ?_
  refine (congrArg (fun z => algebraMap D.host.F (AF D.host.F) (1 / 2) * Algebra.trace (AF D.host.F) (AE D) z) h).trans ?_
  rw [LinearMap.map_neg, mul_neg]

theorem qT_eq (S : HSp D) {T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ) (c : skewA D ρ) (y : Mx D S.rank ρ) :
    d.qT S c y = -(algebraMap D.host.F (AF D.host.F) (1 / 2) *
      Algebra.trace (AF D.host.F) (AE D) ((incA D D.host.xi0⁻¹ • (adj y * (gA S * y))) * c.1).trace) := by
  have h1 : mt T (d.nC c)⁻¹ * d.jY = d.jY + d.jX * (-c.1) := by
    rw [d.nC_inv]; exact d.nC_jY (-c)
  have h2 : incA D (-D.host.xi0⁻¹) = -incA D D.host.xi0⁻¹ := RingHom.map_neg _ _
  have h : mt T (d.nC c)⁻¹ * d.incAdj S y - d.incAdj S y =
      d.incX S (incA D D.host.xi0⁻¹ • (c.1 * (adj y * gA S))) := by
    rw [HypDec.incAdj_apply, HypDec.incY_apply, HypDec.incX_apply, h2]
    exact move_sub h1 _ _
  rw [HypDec.qT, h, symplOH_skew, symplOH, HypDec.symplO_incX_incAdj, trace_cycle_smul]

theorem central_gram : ∀ D : D7, (∀ (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ), (∀ x : Mx D T.rank ρ, GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.starAdj S T (d.extX T x) * x = d.jY * (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.gramSkew T x).map (cA D)) ∧ ∀ (c : skewA D ρ) (x : Mx D T.rank ρ), d.qS T c x = -(algebraMap D.host.F (AF D.host.F) (1 / 2) * Algebra.trace (AF D.host.F) (AE D) ((GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.gramSkew T x).map (cA D) * c.1).trace)) ∧ ∀ (S T T₀ : HSp D) (ρ : ℕ) (d : HypDec T T₀ ρ) (c : skewA D ρ) (y : Mx D S.rank ρ), d.qT S c y = -(algebraMap D.host.F (AF D.host.F) (1 / 2) * Algebra.trace (AF D.host.F) (AE D) ((incA D D.host.xi0⁻¹ • (adj y * (gA S * y))) * c.1).trace) :=
  fun _ => ⟨fun _ _ T _ d => ⟨starAdj_extX_mul T d, qS_eq T d⟩, fun S _ _ _ d => qT_eq S d⟩

end GlobalTheory.CentralGram

end
