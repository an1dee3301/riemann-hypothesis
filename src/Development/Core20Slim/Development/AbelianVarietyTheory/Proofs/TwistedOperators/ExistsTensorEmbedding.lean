module

public import Mathlib
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.SameBlockOfPosC
public import Formalism.LocalRingCardinality.DataTheta
public import Init.Classical
public import Init.Core
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.IsSimpleRing
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.Analysis.CStarAlgebra.Module.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Analysis.Normed.Operator.LinearIsometry
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.FieldTheory.Perfect
public import Mathlib.FieldTheory.Separable
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Notation
public import Mathlib.Order.SetNotation
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.UniformMulAction
public import Mathlib.Topology.Basic
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.MetricSpace.Algebra
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Metrizable.Basic
public import Mathlib.Topology.Metrizable.Uniformity
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible

namespace GlobalTheory.FockTensor

theorem ext_orbit {p q : ℕ} {T : GrpData p q} (D : DSRep T) (u : D.U.H) (hu : u ≠ 0)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (A B : D.U.H →L[ℂ] E)
    (h : ∀ g, A (D.U.π g u) = B (D.U.π g u)) : A = B := by
  let S : Submodule ℂ D.U.H :=
    { carrier := {x | ∀ g, A (D.U.π g x) = B (D.U.π g x)}
      add_mem' := by
        intro a b ha hb g
        simp only [map_add (f := _)]
        rw [ha g, hb g]
      zero_mem' := by intro g; simp
      smul_mem' := by
        intro c a ha g
        simp only [map_smul]
        rw [ha g] }
  have hcl : IsClosed (S : Set D.U.H) := by
    have : (S : Set D.U.H) = ⋂ g, {x | A (D.U.π g x) = B (D.U.π g x)} := by
      ext x; simp only [Set.mem_iInter]; rfl
    rw [this]
    exact isClosed_iInter fun g => isClosed_eq (by fun_prop) (by fun_prop)
  have hinv : ∀ g, ∀ x ∈ S, D.U.π g x ∈ S := by
    intro g x hx g'
    have := hx (g' * g)
    rw [map_mul] at this
    exact this
  rcases D.irred S hcl hinv with h0 | h1
  · have : u ∈ S := h
    rw [h0] at this
    exact absurd ((Submodule.mem_bot ℂ).1 this) hu
  · ext x
    have hx : x ∈ S := by rw [h1]; trivial
    have := hx 1
    rw [map_one] at this
    exact this

theorem isHomG_ext {p q : ℕ} {T : GrpData p q} (D : DSRep T) (πU : URep T) (u : D.U.H)
    (hu : u ≠ 0) (A B : D.U.H →L[ℂ] πU.H) (hA : ∀ g x, A (D.U.π g x) = πU.π g (A x))
    (hB : ∀ g x, B (D.U.π g x) = πU.π g (B x)) (h : A u = B u) : A = B :=
  ext_orbit D u hu A B fun g => by rw [hA, hB, h]

theorem exists_tensor_embedding :
    ∀ (p q : ℕ) (T : GrpData p q) (D : DSRep T) (πU : URep T) (v : D.HK.V), ‖D.ι v‖ = 1 → ∀ (K : Type) [NormedAddCommGroup K] [InnerProductSpace ℂ K] (j : K →ₗᵢ[ℂ] πU.H), (∀ g y y', inner ℂ (j y) (πU.π g (j y')) = mcoef D v g * inner ℂ y y') → (∀ y, ∃ io : D.U.H →L[ℂ] πU.H, IsHomG D πU io ∧ io (D.ι v) = j y) → ∃ Tm : D.U.H →L[ℂ] K →L[ℂ] πU.H, (∀ x x' y y', inner ℂ (Tm x y) (Tm x' y') = inner ℂ x x' * inner ℂ y y') ∧ (∀ y, Tm (D.ι v) y = j y) ∧ (∀ g x y, πU.π g (Tm x y) = Tm (D.U.π g x) y) ∧ ∀ (R : πU.H →L[ℂ] πU.H) (S : K →L[ℂ] K), (∀ g z, R (πU.π g z) = πU.π g (R z)) → (∀ y, R (j y) = j (S y)) → ∀ x y, R (Tm x y) = Tm x (S y) := by
  intro p q T D πU v hv K _ _ j hj hex
  choose io hio hiov using hex
  have hu : D.ι v ≠ 0 := by
    intro h; rw [h, norm_zero] at hv; exact zero_ne_one hv
  have hG : ∀ y g x, io y (D.U.π g x) = πU.π g (io y x) := fun y g x =>
    congrArg (fun f : D.U.H →L[ℂ] πU.H => f x) (hio y g)
  have key1 : ∀ y y' x', inner ℂ (j y) (io y' x') = inner ℂ (D.ι v) x' * inner ℂ y y' := by
    intro y y' x'
    have := ext_orbit D (D.ι v) hu ((innerSL ℂ (j y)).comp (io y'))
      ((inner ℂ y y' : ℂ) • innerSL ℂ (D.ι v)) (fun g => by
        show inner ℂ (j y) (io y' (D.U.π g (D.ι v))) =
          inner ℂ y y' * inner ℂ (D.ι v) (D.U.π g (D.ι v))
        rw [hG, hiov, hj, mcoef, mul_comm])
    have h2 := congrArg (fun f : D.U.H →L[ℂ] ℂ => f x') this
    rw [mul_comm]
    exact h2
  have key2 : ∀ y y' g x', inner ℂ (io y (D.U.π g (D.ι v))) (io y' x') =
      inner ℂ (D.U.π g (D.ι v)) x' * inner ℂ y y' := by
    intro y y' g x'
    rw [hG, hiov, inner_pi_left, ← hG, key1, inner_pi_left]
  have key : ∀ x x' y y', inner ℂ (io y x) (io y' x') = inner ℂ x x' * inner ℂ y y' := by
    intro x x' y y'
    have := ext_orbit D (D.ι v) hu ((innerSL ℂ (io y x)).comp (io y'))
      ((inner ℂ y y' : ℂ) • innerSL ℂ x) (fun g => by
        show inner ℂ (io y x) (io y' (D.U.π g (D.ι v))) =
          inner ℂ y y' * inner ℂ x (D.U.π g (D.ι v))
        rw [← inner_conj_symm, key2, map_mul, inner_conj_symm, inner_conj_symm, mul_comm])
    have h2 := congrArg (fun f : D.U.H →L[ℂ] ℂ => f x') this
    rw [mul_comm]
    exact h2
  have hnorm : ∀ x y, ‖io y x‖ ≤ 1 * ‖x‖ * ‖y‖ := by
    intro x y
    have h := key x x y y
    rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
    have h' : ‖io y x‖ ^ 2 = (‖x‖ * ‖y‖) ^ 2 := by
      rw [mul_pow]; exact_mod_cast h
    have := (pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h'
    rw [this, one_mul]
  have hadd : ∀ y y', io (y + y') = io y + io y' := fun y y' =>
    isHomG_ext D πU _ hu _ _ (hG _) (fun g x => by
      show io y (D.U.π g x) + io y' (D.U.π g x) = πU.π g (io y x + io y' x)
      rw [hG, hG, map_add (f := _)]) (by
      show io (y + y') (D.ι v) = io y (D.ι v) + io y' (D.ι v)
      rw [hiov, hiov, hiov, map_add (f := _)])
  have hsmul : ∀ (c : ℂ) y, io (c • y) = c • io y := fun c y =>
    isHomG_ext D πU _ hu _ _ (hG _) (fun g x => by
      show c • io y (D.U.π g x) = πU.π g (c • io y x)
      rw [hG, map_smul]) (by
      show io (c • y) (D.ι v) = c • io y (D.ι v)
      rw [hiov, hiov, map_smul])
  let L : D.U.H →ₗ[ℂ] K →ₗ[ℂ] πU.H := LinearMap.mk₂ ℂ (fun x y => io y x)
    (fun a b y => map_add _ _ _) (fun c a y => map_smul _ _ _)
    (fun x a b => by rw [hadd]; rfl) (fun c x a => by rw [hsmul]; rfl)
  refine ⟨LinearMap.mkContinuous₂ L 1 hnorm, key, hiov, fun g x y => (hG y g x).symm, ?_⟩
  intro R S hR hS x y
  have := isHomG_ext D πU _ hu (R.comp (io y)) (io (S y)) (fun g x => by
      show R (io y (D.U.π g x)) = πU.π g (R (io y x))
      rw [hG, hR]) (hG _) (by
      show R (io y (D.ι v)) = _
      rw [hiov, hiov, hS])
  exact congrArg (fun f : D.U.H →L[ℂ] πU.H => f x) this

end GlobalTheory.FockTensor
