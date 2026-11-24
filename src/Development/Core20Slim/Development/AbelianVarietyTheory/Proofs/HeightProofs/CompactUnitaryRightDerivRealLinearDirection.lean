module

public import Mathlib
public import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
public import Development.Core20Slim.Development.AbelianVarietyTheory.BlockTheory.HeightDefect.FinitePartTypes
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqExistsIffDsExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqUniqueOfClassification
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasTypeAllAddOfEquiv
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneAddHsConjLe
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoefBoundOfCasselmanWallach
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.HeightProofs.FiniteDimensionalPolyV
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.HeightProofs.ContDiffMatrixRightInvariantDerivative
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
public import Formalism.RealPlaceAnalysis.Complexify
public import Formalism.RealPlaceAnalysis.SmoothOnGVIff
public import Init.Core
public import Init.Data.Bool
public import Init.Data.Int.Basic
public import Init.Data.List.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.GroupWithZero.Action
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Algebra.Star.BigOperators
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Star
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.Real.Star
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Algebra
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KFourier MeasureTheory

noncomputable section

namespace GlobalTheory.KFourier

open Matrix

variable {n : ℕ}

theorem inK_zero' (ε : Fin n → Bool) : inK ε (0 : Mx n) := by
  refine ⟨?_, ?_⟩
  · show (0 : Mx n)ᴴ * Jm ε + Jm ε * 0 = 0
    simp
  · simp

theorem inK_add'' {ε : Fin n → Bool} {X Y : Mx n} (hX : inK ε X) (hY : inK ε Y) : inK ε (X + Y) := by
  obtain ⟨h1, h2⟩ := hX
  obtain ⟨h3, h4⟩ := hY
  refine ⟨?_, ?_⟩
  · have h1' : Xᴴ * Jm ε + Jm ε * X = 0 := h1
    have h3' : Yᴴ * Jm ε + Jm ε * Y = 0 := h3
    show (X + Y)ᴴ * Jm ε + Jm ε * (X + Y) = 0
    rw [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add]
    calc Xᴴ * Jm ε + Yᴴ * Jm ε + (Jm ε * X + Jm ε * Y)
        = (Xᴴ * Jm ε + Jm ε * X) + (Yᴴ * Jm ε + Jm ε * Y) := by abel
      _ = 0 := by rw [h1', h3', add_zero]
  · rw [Matrix.add_mul, Matrix.mul_add, h2, h4]

theorem inK_sum_real {ε : Fin n → Bool} {r : ℕ} (X : Fin r → Mx n) (c : Fin r → ℝ) (hX : ∀ j, inK ε (X j)) :
    inK ε (∑ j, (c j : ℂ) • X j) := by
  classical
  refine Finset.sum_induction _ (inK ε) (fun _ _ ha hb => inK_add'' ha hb) (inK_zero' ε) ?_
  intro j _
  exact inK_smul_real ε (hX j) (c j)

def entryDer (ε : Fin n → Bool) (k : KG ε) (a b : Fin n) : Mx n →ₗ[ℝ] ℂ where
  toFun Y := ∑ l, toMK k a l * Y l b
  map_add' Y Z := by
    simp only [Matrix.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' r Y := by
    simp only [Matrix.smul_apply, RingHom.id_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [Complex.real_smul]
    ring

def entryDerStar (ε : Fin n → Bool) (k : KG ε) (a b : Fin n) : Mx n →ₗ[ℝ] ℂ where
  toFun Y := star (∑ l, toMK k a l * Y l b)
  map_add' Y Z := by
    simp only [Matrix.add_apply, mul_add, Finset.sum_add_distrib, star_add]
  map_smul' r Y := by
    simp only [Matrix.smul_apply, RingHom.id_apply, Complex.real_smul]
    simp only [star_sum, Finset.mul_sum, star_mul', Complex.star_def, map_mul, Complex.conj_ofReal]
    refine Finset.sum_congr rfl fun l _ => ?_
    ring

theorem hasDerivAt_coord_lin {ε : Fin n → Bool} (c : Fin n × Fin n × Bool) :
    ∃ D : KG ε → Mx n →ₗ[ℝ] ℂ, ∀ (k : KG ε) (Y : Mx n), inK ε Y →
      HasDerivAt (fun t : ℝ => coord ε c (k * expK ε Y t)) (D k Y) 0 := by
  obtain ⟨a, b, f⟩ := c
  have hent : ∀ (k : KG ε) (Y : Mx n), inK ε Y → HasDerivAt (fun t : ℝ => (toMK (k * expK ε Y t)) a b)
      (∑ l, toMK k a l * Y l b) 0 := by
    intro k Y hY
    have e : (fun t : ℝ => (toMK (k * expK ε Y t)) a b) =
        fun t : ℝ => ∑ l, toMK k a l * (NormedSpace.exp ((t : ℂ) • Y)) l b := by
      funext t; simp only [toMK_mul, toMK_expK hY, Matrix.mul_apply]
    rw [e]
    exact HasDerivAt.fun_sum fun l _ => (hasDerivAt_exp_entry_real Y l b).const_mul _
  cases f
  · refine ⟨fun k => entryDerStar ε k a b, fun k Y hY => ?_⟩
    have h := (hent k Y hY).star
    have e1 : (fun t : ℝ => coord ε (a, b, false) (k * expK ε Y t)) =
        fun t => star ((toMK (k * expK ε Y t)) a b) := by
      funext t; simp [coord]
    rw [e1]; exact h
  · refine ⟨fun k => entryDer ε k a b, fun k Y hY => ?_⟩
    have e1 : (fun t : ℝ => coord ε (a, b, true) (k * expK ε Y t)) =
        fun t => (toMK (k * expK ε Y t)) a b := by
      funext t; simp [coord]
    rw [e1]; exact hent k Y hY

theorem hasDerivAt_mono_lin {ε : Fin n → Bool} (s : List (Fin n × Fin n × Bool)) :
    ∃ D : KG ε → Mx n →ₗ[ℝ] ℂ, ∀ (k : KG ε) (Y : Mx n), inK ε Y →
      HasDerivAt (fun t : ℝ => mono ε s (k * expK ε Y t)) (D k Y) 0 := by
  induction s with
  | nil =>
    refine ⟨0, fun k Y _ => ?_⟩
    simpa [mono] using hasDerivAt_const (0 : ℝ) (1 : ℂ)
  | cons c s ih =>
    obtain ⟨Dc, hc⟩ := hasDerivAt_coord_lin (ε := ε) c
    obtain ⟨Ds, hs⟩ := ih
    refine ⟨fun k => mono ε s k • Dc k + coord ε c k • Ds k, fun k Y hY => ?_⟩
    have h := (hc k Y hY).mul (hs k Y hY)
    have e : (fun t : ℝ => mono ε (c :: s) (k * expK ε Y t)) =
        fun t => coord ε c (k * expK ε Y t) * mono ε s (k * expK ε Y t) := by
      funext t; simp [mono]
    rw [e]
    rw [coord_mul_expK_zero hY, mono_mul_expK_zero hY] at h
    refine h.congr_deriv ?_
    simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    ring

theorem hasDerivAt_lin_of_mem {ε : Fin n → Bool} {d : ℕ} {φ : KG ε → ℂ} (hφ : φ ∈ polyV ε d) :
    ∃ D : KG ε → Mx n →ₗ[ℝ] ℂ, ∀ (k : KG ε) (Y : Mx n), inK ε Y →
      HasDerivAt (fun t : ℝ => φ (k * expK ε Y t)) (D k Y) 0 := by
  induction hφ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨s, -, rfl⟩ := hx
    exact hasDerivAt_mono_lin s
  | zero =>
    exact ⟨0, fun k Y _ => by simpa using hasDerivAt_const (0 : ℝ) (0 : ℂ)⟩
  | add x y _ _ hx hy =>
    obtain ⟨D₁, d₁⟩ := hx
    obtain ⟨D₂, d₂⟩ := hy
    exact ⟨D₁ + D₂, fun k Y hY => (d₁ k Y hY).add (d₂ k Y hY)⟩
  | smul a x _ hx =>
    obtain ⟨D, dD⟩ := hx
    exact ⟨a • D, fun k Y hY => by simpa using (dD k Y hY).const_mul a⟩

theorem rder_real_linear {n : ℕ} (ε : Fin n → Bool) (d : ℕ) (φ : KG ε → ℂ) (hφ : φ ∈ polyV ε d)
    {r : ℕ} (X : Fin r → Mx n) (c : Fin r → ℝ) (hX : ∀ j, inK ε (X j)) :
    rder ε [∑ j, (c j : ℂ) • X j] φ = ∑ j, (c j : ℂ) • rder ε [X j] φ := by
  obtain ⟨D, hD⟩ := hasDerivAt_lin_of_mem hφ
  have hr : ∀ (Y : Mx n), inK ε Y → ∀ k, rder ε [Y] φ k = D k Y := by
    intro Y hY k
    rw [rder_cons, rder_nil]
    exact (hD k Y hY).deriv
  funext k
  rw [hr _ (inK_sum_real X c hX) k, Finset.sum_apply]
  have e : (∑ j, (c j : ℂ) • X j) = ∑ j, c j • X j :=
    Finset.sum_congr rfl fun j _ => Complex.coe_smul (c j) (X j)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [e, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, Pi.smul_apply, hr _ (hX j) k, Complex.real_smul, smul_eq_mul]

end GlobalTheory.KFourier

end
