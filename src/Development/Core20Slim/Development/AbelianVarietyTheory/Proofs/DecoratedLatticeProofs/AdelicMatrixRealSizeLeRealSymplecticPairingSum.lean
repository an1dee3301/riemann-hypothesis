module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.LatticeFrames.RealSizeNonneg
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
public import Batteries.Logic
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
public import Formalism.LocalToGlobal.IndefiniteReal.LinksExistW
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.ByCases
public import Init.Core
public import Init.Data.Bool
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.GroupWithZero.Units.Lemmas
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Logic.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Basis
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Lattice
public import Mathlib.Tactic.FieldSimp.Lemmas
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff

namespace GlobalTheory.RealPairBound

theorem trace_conjT_mul_single {r s : ℕ} (X : Matrix (Fin r) (Fin s) ℂ) (i : Fin r) (j : Fin s) (a : ℂ) :
    (Xᴴ * Matrix.single i j a).trace = star (X i j) * a := by
  simp [Matrix.trace, Matrix.mul_apply, Matrix.single_apply, Matrix.conjTranspose_apply, ite_and]

theorem gramAt_det_ne (D : D7) (T : HSp D) (τ : D.what₂.Tau) : (gramAt D T τ).det ≠ 0 := by
  rw [gramAt, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact (map_ne_zero _).2 (Formalism.L2.Theta.gram_det_ne T)

theorem pair_single (D : D7) (T : HSp D) {ρ : ℕ} (τ : D.what₂.Tau) (X : Matrix (Fin T.rank) (Fin ρ) ℂ)
    (i : Fin T.rank) (j : Fin ρ) (a : ℂ) :
    tauE D τ D.host.xi0 * (Xᴴ * gramAt D T τ * ((gramAt D T τ)⁻¹ * Matrix.single i j a)).trace
      = tauE D τ D.host.xi0 * (star (X i j) * a) := by
  have hu : IsUnit (gramAt D T τ).det := isUnit_iff_ne_zero.2 (gramAt_det_ne D T τ)
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc (gramAt D T τ), Matrix.mul_nonsing_inv _ hu, Matrix.one_mul,
    trace_conjT_mul_single]

theorem realSize_le_pairing : ∀ (D : D7) (θ : InfFam D) (T : HSp D) (ρ : ℕ), ∃ (k : ℕ) (τs : Fin k → D.what₂.Tau)
    (zs : Fin k → Matrix (Fin T.rank) (Fin ρ) ℂ) (C : ℝ), ∀ x : Mx D T.rank ρ,
      realSize θ x ≤ C * ∑ i, |2 * (tauE D (τs i) D.host.xi0 * ((compAt θ (τs i) x)ᴴ * gramAt D T (τs i) * zs i).trace).re| := by
  intro D θ T ρ
  classical
  let c : D.what₂.Tau → ℂ := fun τ => tauE D τ D.host.xi0
  have hc : ∀ τ, c τ ≠ 0 := fun τ => (map_ne_zero _).2 (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D)
  let α : D.what₂.Tau → Bool → ℂ := fun τ b => if b then (c τ)⁻¹ * Complex.I else (c τ)⁻¹
  let z : D.what₂.Tau × Fin T.rank × Fin ρ × Bool → Matrix (Fin T.rank) (Fin ρ) ℂ :=
    fun p => (gramAt D T p.1)⁻¹ * Matrix.single p.2.1 p.2.2.1 (α p.1 p.2.2.2)
  let e := (Fintype.equivFin (D.what₂.Tau × Fin T.rank × Fin ρ × Bool)).symm
  refine ⟨_, fun n => (e n).1, fun n => z (e n), 1, fun x => ?_⟩
  rw [one_mul]
  let v : D.what₂.Tau × Fin T.rank × Fin ρ × Bool → ℝ := fun p =>
    |2 * (tauE D p.1 D.host.xi0 * ((compAt θ p.1 x)ᴴ * gramAt D T p.1 * z p).trace).re|
  change realSize θ x ≤ ∑ n, v (e n)
  rw [Equiv.sum_comp e v, Fintype.sum_prod_type, realSize]
  refine Finset.sum_le_sum fun τ _ => ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [Fintype.sum_bool]
  have hv : ∀ b, v (τ, i, j, b) = |2 * (c τ * (star (compAt θ τ x i j) * α τ b)).re| := fun b => by
    simp only [v, z]
    rw [pair_single]
  rw [hv, hv]
  have h1 : c τ * (star (compAt θ τ x i j) * α τ true) = star (compAt θ τ x i j) * Complex.I := by
    simp only [α, if_true]
    field_simp [hc τ]
  have h0 : c τ * (star (compAt θ τ x i j) * α τ false) = star (compAt θ τ x i j) := by
    simp only [α, Bool.false_eq_true, if_false]
    field_simp [hc τ]
  rw [h1, h0]
  have hn := Complex.norm_le_abs_re_add_abs_im (compAt θ τ x i j)
  simp only [Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.I_re, Complex.I_im,
    abs_mul, mul_zero, mul_one, zero_sub, abs_neg, abs_two]
  linarith [abs_nonneg (compAt θ τ x i j).re, abs_nonneg (compAt θ τ x i j).im]

end GlobalTheory.RealPairBound
