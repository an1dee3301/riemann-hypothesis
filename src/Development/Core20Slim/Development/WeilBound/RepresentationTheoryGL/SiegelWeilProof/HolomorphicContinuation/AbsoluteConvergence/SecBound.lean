module

public import Mathlib
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.ContinuousSecondCayleyBlockMap
public import Batteries.Logic
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.DerivativeVacuumDilationsAlt
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.FarRightAlt
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobData
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.NullSec
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Order.Lattice
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.Extr
public import Mathlib.Order.Lattice
public import Mathlib.Order.MinMax
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.Tactic.FieldSimp.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Positivity.Core
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Bases
public import Mathlib.Topology.ContinuousOn
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Order.OrderClosed
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped NNReal

namespace PositivityTheory.Rg.Sw.AbsSt.Far

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt

variable {m n : ℕ} {ε : Fin m → Bool} {c t : ℝ} {p q : ℕ} {e : ℤ} {sL : PX m n →ₗ[ℂ] (GR n → ℂ)}
  {ρ : GR n → PX m n →ₗ[ℂ] PX m n}

theorem sL_bound (hI : Iwa) (hM : Mult) (hD : CayleyBlocksInvertible) (hL : LocData ε c t p q e sL ρ) (Q : PX m n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : GR n, ‖sL Q y‖ ≤ C * ‖F0 p q e y‖ := by
  have hK := isCompact_KR (n := n)
  have hs : Continuous (sL Q) := hL.cont Q
  have hF : Continuous (F0 (n := n) p q e) := continuous_weight_factor hD p q e
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hs.continuousOn
  have hne : ((KR n : Subgroup (GR n)) : Set (GR n)).Nonempty := ⟨1, (KR n).one_mem⟩
  obtain ⟨k0, -, hmin⟩ := hK.exists_isMinOn hne hF.norm.continuousOn
  set δ := ‖F0 p q e k0‖ with hδdef
  have hδ : 0 < δ := norm_pos_iff.mpr (weight_factor_ne_zero hD p q e k0)
  refine ⟨max B 0 / δ, div_nonneg (le_max_right _ _) hδ.le, fun y => ?_⟩
  obtain ⟨u, k, hu, hk, rfl⟩ := hI n y
  have hmk : δ ≤ ‖F0 p q e k‖ := hmin hk
  calc ‖sL Q (u * k)‖ = ‖F0 p q e u‖ * ‖sL Q k‖ := by rw [hL.law Q u k hu, norm_mul]
    _ ≤ ‖F0 p q e u‖ * max B 0 :=
        mul_le_mul_of_nonneg_left ((hB k hk).trans (le_max_left _ _)) (norm_nonneg _)
    _ = (max B 0 / δ) * (‖F0 p q e u‖ * δ) := by field_simp
    _ ≤ (max B 0 / δ) * (‖F0 p q e u‖ * ‖F0 p q e k‖) := by gcongr
    _ = (max B 0 / δ) * ‖F0 p q e (u * k)‖ := by rw [((hM n p q e).1 u k hk).1, norm_mul]

theorem rpow_le_add {a x₁ x₂ s : ℝ} (ha : 0 < a) (h₁ : x₁ ≤ s) (h₂ : s ≤ x₂) : a ^ s ≤ a ^ x₁ + a ^ x₂ := by
  rcases le_total 1 a with h | h
  · exact (Real.rpow_le_rpow_of_exponent_le h h₂).trans (le_add_of_nonneg_left (Real.rpow_nonneg ha.le _))
  · exact (Real.rpow_le_rpow_of_exponent_ge ha h h₁).trans (le_add_of_nonneg_right (Real.rpow_nonneg ha.le _))

section Glob

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
  [SecondCountableTopology G] {Pp Γ : Subgroup G} {ι : GR n →* G} {s₀ : ℂ} {Ht : G → ℝ≥0}
  {sec I : PX m n →ₗ[ℂ] (G → ℂ)} {Λ : Set ((G → ℂ) → ℂ)}

theorem Ht_pos (hD : CayleyBlocksInvertible) (hG : GlobData ε c sL ρ G Pp Γ ι s₀ Ht sec I Λ) (x : G) : 0 < (Ht x : ℝ) := by
  obtain ⟨x₀, y, S, r, hr, rfl, h⟩ := hG.split x
  rw [(h y).1]
  exact mul_pos hr (hLoc_pos hD y)

theorem sec_bound (hI : Iwa) (hM : Mult) (hD : CayleyBlocksInvertible) (hL : LocData ε c t p q e sL ρ)
    (hG : GlobData ε c sL ρ G Pp Γ ι s₀ Ht sec I Λ) (Q : PX m n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : G, ‖sec Q x‖ ≤ C * ‖sec 1 x‖ := by
  obtain ⟨C, hC0, hC⟩ := sL_bound hI hM hD hL Q
  refine ⟨C, hC0, fun x => ?_⟩
  obtain ⟨x₀, y, S, r, hr, rfl, h⟩ := hG.split x
  rw [(h y).2 Q, (h y).2 1, hL.vac y, norm_mul, norm_mul]
  calc ‖S‖ * ‖sL Q y‖ ≤ ‖S‖ * (C * ‖F0 p q e y‖) := mul_le_mul_of_nonneg_left (hC y) (norm_nonneg _)
    _ = C * (‖S‖ * ‖F0 p q e y‖) := by ring

theorem norm_hz (hD : CayleyBlocksInvertible) (hG : GlobData ε c sL ρ G Pp Γ ι s₀ Ht sec I Λ) (z : ℂ) (Q : PX m n) (x : G) :
    ‖hz Ht sec s₀ z Q x‖ = (Ht x : ℝ) ^ (z.re - s₀.re) * ‖sec Q x‖ := by
  unfold hz
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (Ht_pos hD hG x), Complex.sub_re]

end Glob

end PositivityTheory.Rg.Sw.AbsSt.Far
