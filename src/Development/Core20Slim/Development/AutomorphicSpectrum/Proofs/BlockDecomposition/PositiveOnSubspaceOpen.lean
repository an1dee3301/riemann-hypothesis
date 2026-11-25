module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableOfMulUnimodular
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
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
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.MulAction
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Filter.Tendsto
public import Mathlib.Order.Lattice
public import Mathlib.RingTheory.Bialgebra.Basic
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Algebra.Star
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
public import Mathlib.Topology.MetricSpace.Pseudo.Pi
public import Mathlib.Topology.Neighborhoods
public import Mathlib.Topology.Order.Basic
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open scoped Matrix Topology

namespace GlobalTheory.CompanionTheory.WeilSiegel.NoFrame

theorem isOpen_posOn (n : ℕ) (ε : ℝ) (S : Submodule ℂ (Fin n → ℂ)) :
    IsOpen {Z : Matrix (Fin n) (Fin n) ℂ | PosOn ε Z S} := by
  set K : Set (Fin n → ℂ) := (S : Set (Fin n → ℂ)) ∩ Metric.sphere 0 1 with hK
  have hKc : IsCompact K := (isCompact_sphere 0 1).inter_left S.closed_of_finiteDimensional
  let F : Matrix (Fin n) (Fin n) ℂ → (Fin n → ℂ) → ℝ := fun Z w => ε * (star w ⬝ᵥ Z.mulVec w).re
  have hF : Continuous (fun p : Matrix (Fin n) (Fin n) ℂ × (Fin n → ℂ) => F p.1 p.2) :=
    continuous_const.mul (Complex.continuous_re.comp
      ((continuous_snd.star).dotProduct (continuous_fst.matrix_mulVec continuous_snd)))
  have hscale : ∀ (Z : Matrix (Fin n) (Fin n) ℂ) (w : Fin n → ℂ) (c : ℝ),
      F Z ((c : ℂ) • w) = c ^ 2 * F Z w := by
    intro Z w c
    simp only [F, Matrix.mulVec_smul, dotProduct_smul, star_smul, smul_dotProduct, smul_eq_mul,
      Complex.star_def, Complex.conj_ofReal, Complex.re_ofReal_mul]
    ring
  have heq : {Z : Matrix (Fin n) (Fin n) ℂ | PosOn ε Z S} = {Z | ∀ w ∈ K, 0 < F Z w} := by
    ext Z
    constructor
    · rintro hZ w ⟨hwS, hw1⟩
      refine hZ w hwS ?_
      rintro rfl
      simp at hw1
    · intro hZ w hwS hw0
      have hn : 0 < ‖w‖ := norm_pos_iff.mpr hw0
      have hmem : ((‖w‖⁻¹ : ℝ) : ℂ) • w ∈ K := by
        refine ⟨S.smul_mem _ hwS, ?_⟩
        rw [mem_sphere_zero_iff_norm, norm_smul, Complex.norm_real, Real.norm_eq_abs,
          abs_inv, abs_norm, inv_mul_cancel₀ hn.ne']
      have h2 := hZ _ hmem
      rw [hscale] at h2
      exact pos_of_mul_pos_right h2 (by positivity)
  rw [heq, isOpen_iff_mem_nhds]
  intro Z₀ hZ₀
  exact hKc.eventually_forall_of_forall_eventually fun w hw =>
    (hF.tendsto (Z₀, w)).eventually (lt_mem_nhds (hZ₀ w hw))

end GlobalTheory.CompanionTheory.WeilSiegel.NoFrame
