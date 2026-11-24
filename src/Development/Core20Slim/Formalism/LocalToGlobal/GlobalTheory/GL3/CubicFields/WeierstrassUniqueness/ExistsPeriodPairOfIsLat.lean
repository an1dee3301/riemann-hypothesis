module

public import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.ComplexMultiplication.UniqInvOfLat
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
public import Init.Classical
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Int.Lemmas
public import Init.Data.Int.Order
public import Init.Data.List.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Indicator
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Logic.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.CoeSort
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.SummationFilter
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5

open NumberField Classical
open Formalism.BasicNotions (D7)
open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity (IsLat jL Uniformization CMTransitive)
open Formalism.MainNotions.TaylorLogMetric (lamOf)


theorem eisG_eq_G_of_lattice (Λ : AddSubgroup ℂ) (L : PeriodPair) (hL : (L.lattice : Set ℂ) = Λ)
    (n : ℕ) (hn : n ≠ 0) : Formalism.MainNotions.TaylorLogMetric.eisG Λ n = L.G (2 * n) := by
  unfold Formalism.MainNotions.TaylorLogMetric.eisG PeriodPair.G
  have h1 := tsum_subtype ({w : ℂ | w ∈ Λ ∧ w ≠ 0}) (fun w : ℂ => 1 / w ^ (2 * n))
  have h2 := tsum_subtype ((L.lattice : Set ℂ)) (fun w : ℂ => (w ^ (2 * n))⁻¹)
  refine h1.trans (Eq.trans ?_ h2.symm)
  congr 1
  funext x
  by_cases hx : x = 0
  · subst hx
    have h0 : (0 : ℂ) ^ (2 * n) = 0 := zero_pow (by omega)
    simp [Set.indicator, h0]
  · have hm : x ∈ L.lattice ↔ x ∈ Λ := by
      rw [← SetLike.mem_coe, hL, SetLike.mem_coe]
    simp only [Set.indicator, Set.mem_setOf_eq, hx, ne_eq, not_false_eq_true, and_true,
      SetLike.mem_coe, hm, one_div]

theorem g2_g3_eq_periodPair (Λ : AddSubgroup ℂ) (L : PeriodPair) (hL : (L.lattice : Set ℂ) = Λ) :
    Formalism.MainNotions.TaylorLogMetric.g2 Λ = L.g₂ ∧ Formalism.MainNotions.TaylorLogMetric.g3 Λ = L.g₃ := by
  refine ⟨?_, ?_⟩
  · unfold Formalism.MainNotions.TaylorLogMetric.g2 PeriodPair.g₂
    rw [eisG_eq_G_of_lattice Λ L hL 2 (by norm_num)]
  · unfold Formalism.MainNotions.TaylorLogMetric.g3 PeriodPair.g₃
    rw [eisG_eq_G_of_lattice Λ L hL 3 (by norm_num)]

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5

end
