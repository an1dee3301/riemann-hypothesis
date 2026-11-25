module

public import Mathlib
public import Batteries.Logic
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Order.Lemmas
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Ring.Unbundled.Basic
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Order.ZeroLEOne
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Algebra.Star.Pi
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Module.RCLike.Real
public import Mathlib.Analysis.Normed.MulAction
public import Mathlib.Analysis.Normed.Order.Lattice
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.IsEmpty.Basic
public import Mathlib.Basic.IsEmpty.Defs
public import Mathlib.Basic.Logic.Basic
public import Mathlib.Basic.Nontrivial.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.Real.Star
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.Extr
public import Mathlib.Order.Lattice
public import Mathlib.Order.RelClasses
public import Mathlib.Tactic.FieldSimp.Lemmas
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Star
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.ContinuousOn
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.EMetricSpace.Defs
public import Mathlib.Topology.GDelta.MetrizableSpace
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.MetricSpace.Pseudo.Pi
public import Mathlib.Topology.Metrizable.Uniformity
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Order.OrderClosed
public import Mathlib.Topology.Separation.Basic
public import Mathlib.Topology.Separation.CompletelyRegular
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

theorem UpperTheory.Reformulated.B.CoerciveOfPositiveDefinite.exists_coercive_of_posDef.{u_1} :
    ∀ {ι : Type u_1} [inst : Fintype ι] {P : Matrix ι ι Complex},
      @Matrix.PosDef ι Complex Complex.instRing Complex.partialOrder Complex.instStarRing P →
        ∃ (c : Real),
          And (@LT.lt Real Real.instLT (@OfNat.ofNat Real (nat_lit 0) (@Zero.toOfNat0 Real Real.instZero)) c)
            (∀ (z : ι → Complex) (j : ι),
              @LE.le Real Real.instLE
                (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) c
                  (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid)))
                    (@Norm.norm Complex Complex.instNorm (z j)) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                (@dotProduct ι Complex inst Complex.instMul Complex.instAddCommMonoid
                    (@Star.star (ι → Complex)
                      (@Pi.instStarForall ι (fun (a : ι) ↦ Complex) fun (i : ι) ↦
                        @InvolutiveStar.toStar Complex
                          (@StarAddMonoid.toInvolutiveStar Complex
                            (@AddCommMonoid.toAddMonoid Complex
                              (@NonUnitalNonAssocSemiring.toAddCommMonoid Complex
                                (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring Complex
                                  (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing Complex
                                    (@NonUnitalCommRing.toNonUnitalNonAssocCommRing Complex
                                      Complex.instNonUnitalCommRing)))))
                            (@StarRing.toStarAddMonoid Complex
                              (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring Complex
                                (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing Complex
                                  (@NonUnitalCommRing.toNonUnitalNonAssocCommRing Complex Complex.instNonUnitalCommRing)))
                              Complex.instStarRing)))
                      z)
                    (@Matrix.mulVec ι ι Complex
                      (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring Complex
                        (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing Complex
                          (@NonUnitalCommRing.toNonUnitalNonAssocCommRing Complex Complex.instNonUnitalCommRing)))
                      inst P z)).re) := by
  intro ι _ P hP
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨1, one_pos, fun _ j => (hι.false j).elim⟩
  have hcont : Continuous fun z : ι → ℂ => (star z ⬝ᵥ P.mulVec z).re := by
    unfold dotProduct Matrix.mulVec dotProduct
    fun_prop
  have hne : (Metric.sphere (0 : ι → ℂ) 1).Nonempty :=
    NormedSpace.sphere_nonempty.mpr zero_le_one
  obtain ⟨u, hu, hmin⟩ := (isCompact_sphere (0 : ι → ℂ) 1).exists_isMinOn hne hcont.continuousOn
  have hu0 : u ≠ 0 := by
    rintro rfl
    simp at hu
  have hc : 0 < (star u ⬝ᵥ P.mulVec u).re := hP.re_dotProduct_pos hu0
  refine ⟨_, hc, fun z j => ?_⟩
  rcases eq_or_ne z 0 with rfl | hz
  · simp
  have hr : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hw : (‖z‖⁻¹ • z) ∈ Metric.sphere (0 : ι → ℂ) 1 := by
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hr.ne']
  have h1 : (star u ⬝ᵥ P.mulVec u).re ≤ (star (‖z‖⁻¹ • z) ⬝ᵥ P.mulVec (‖z‖⁻¹ • z)).re := hmin hw
  have h2 : (star (‖z‖⁻¹ • z) ⬝ᵥ P.mulVec (‖z‖⁻¹ • z)).re
      = ‖z‖⁻¹ * (‖z‖⁻¹ * (star z ⬝ᵥ P.mulVec z).re) := by
    rw [star_smul, star_trivial, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul,
      Complex.smul_re, Complex.smul_re, smul_eq_mul, smul_eq_mul]
  have h3 : (star u ⬝ᵥ P.mulVec u).re * ‖z‖ ^ 2 ≤ (star z ⬝ᵥ P.mulVec z).re := by
    rw [h2] at h1
    calc (star u ⬝ᵥ P.mulVec u).re * ‖z‖ ^ 2
        ≤ ‖z‖⁻¹ * (‖z‖⁻¹ * (star z ⬝ᵥ P.mulVec z).re) * ‖z‖ ^ 2 :=
          mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
      _ = (star z ⬝ᵥ P.mulVec z).re := by field_simp
  exact (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (norm_nonneg _) (norm_le_pi_norm z j) 2) hc.le).trans h3
