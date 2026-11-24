module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AbelianVarietyTheory.Definitions.Foundations.SecondCountableAndT2LocalField
public import Init.Classical
public import Init.Core
public import Init.Data.Nat.Lemmas
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Indicator
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Quot
public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.RingTheory.Valuation.Integers
public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
public import Mathlib.Topology.Algebra.Support
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Clopen
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Topology.Neighborhoods
public import Mathlib.Topology.Separation.Hausdorff

@[expose] public section

open MeasureTheory Matrix ValuativeRel

noncomputable section
namespace GlobalTheory.HeisUnit

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]


variable (k) in
def intInd (n d : ℕ) : Matrix (Fin n) (Fin d) k → ℂ := Set.indicator {Y | ∀ i j, Y i j ∈ 𝒪[k]} 1

def diagAt {n : ℕ} (x : kˣ) (i0 : Fin n) : GL (Fin n) k := SplitFlip.diagGL fun i => if i = i0 then x else 1

def cosetRep {n d : ℕ} (ϖ : kˣ) (i0 : Fin n) (T : Fin d → SplitFlip.Res (k := k) 1) : Matrix (Fin n) (Fin d) k :=
  Matrix.of fun i j => if i = i0 then -((ϖ : k)⁻¹ * ((Quotient.out (T j) : 𝒪[k]) : k)) else 0

theorem intInd_mem_SB (n d : ℕ) : intInd k n d ∈ GlobalTheory.WeilM.SB (Matrix (Fin n) (Fin d) k) := by
  obtain ⟨_, _⟩ := SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  have hc : IsCompact {Y : Matrix (Fin n) (Fin d) k | ∀ i j, Y i j ∈ 𝒪[k]} := SplitFlip.isCompact_intMatrix
  have ho : IsOpen {Y : Matrix (Fin n) (Fin d) k | ∀ i j, Y i j ∈ 𝒪[k]} := SplitFlip.isOpen_intMatrix
  have hW : IsClopen {Y : Matrix (Fin n) (Fin d) k | ∀ i j, Y i j ∈ 𝒪[k]} := ⟨hc.isClosed, ho⟩
  refine ⟨?_, HasCompactSupport.intro' hc hW.isClosed fun x hx => Set.indicator_of_notMem hx _⟩
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  by_cases hx : x ∈ {Y : Matrix (Fin n) (Fin d) k | ∀ i j, Y i j ∈ 𝒪[k]}
  · filter_upwards [hW.isOpen.mem_nhds hx] with y hy
    simp only [Set.mem_setOf_eq] at hx
    simp [intInd, Set.indicator_apply, hy, hx]
  · filter_upwards [hW.isClosed.isOpen_compl.mem_nhds hx] with y hy
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq] at hx hy
    simp [intInd, Set.indicator_apply, hy, hx]

theorem intInd_zero (n d : ℕ) : intInd k n d 0 = 1 :=
  Set.indicator_of_mem (show (0 : Matrix (Fin n) (Fin d) k) ∈ {Y | ∀ i j, Y i j ∈ 𝒪[k]} from
    fun _ _ => zero_mem _) _

theorem det_diagAt {n : ℕ} (x : kˣ) (i0 : Fin n) : Matrix.GeneralLinearGroup.det (diagAt x i0) = x := by
  rw [diagAt, SplitFlip.det_diagGL, Fintype.prod_eq_single i0 (fun i hi => if_neg hi), if_pos rfl]

theorem diagAt_val {n : ℕ} (x : kˣ) (i0 : Fin n) :
    (diagAt x i0).val = Matrix.diagonal fun i => if i = i0 then (x : k) else 1 := by
  rw [diagAt, SplitFlip.diagGL_val]
  congr 1; funext i; split_ifs <;> simp

end GlobalTheory.HeisUnit
