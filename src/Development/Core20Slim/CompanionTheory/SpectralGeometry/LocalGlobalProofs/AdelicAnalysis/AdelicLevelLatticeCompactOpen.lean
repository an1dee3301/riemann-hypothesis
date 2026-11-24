module

public import Mathlib
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SumRhoEqTrace
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FiniteAdeleTopologyStatement
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
public import Init.Classical
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Notation.Indicator
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Torsor.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Operations
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Group.Torsor
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Support
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Clopen
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Topology.Neighborhoods
public import Mathlib.Topology.Separation.Basic
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.Separation.Regular

@[expose] public section

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.ThW.Lco

open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core GlobalTheory.CompanionTheory.SW.ThW
open scoped ENNReal NNReal MatrixGroups Kronecker

theorem latN_coe_eq_pi (F : Type) [Field F] [NumberField F] (ι : Type) [Fintype ι] [DecidableEq ι]
    (N : ℕ) : (latN F ι N : Set (ι → A F)) =
      Set.pi Set.univ (fun _ => {x : A F | ∃ y ∈ Oh F, x = (N : A F) * y}) := by
  ext x
  exact ⟨fun h i _ => h i, fun h i => h i (Set.mem_univ i)⟩

theorem isCompact_mul_oh (F : Type) [Field F] [NumberField F] (N : ℕ) :
    IsCompact {x : A F | ∃ y ∈ Oh F, x = (N : A F) * y} := by
  have hOh : IsCompact (Oh F) := (GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F).2.2.2.1
  have heq : {x : A F | ∃ y ∈ Oh F, x = (N : A F) * y} = (fun y => (N : A F) * y) '' Oh F := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, hy, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, hy, rfl⟩
  rw [heq]
  exact hOh.image (continuous_const.mul continuous_id)

theorem main : ∀ (F : Type) [Field F] [NumberField F] (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ),
    0 < N → IsCompact (latN F ι N : Set (ι → A F)) ∧ IsOpen (latN F ι N : Set (ι → A F)) ∧
      ∀ a : ι → F, SB (indC N a) := by
  intro F _ _ ι _ _ N hN
  obtain ⟨-, -, hT2, -, -, -, -, -, -, hOpen⟩ := GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F
  have hC : IsCompact (latN F ι N : Set (ι → A F)) := by
    rw [latN_coe_eq_pi]
    exact isCompact_univ_pi fun _ => isCompact_mul_oh F N
  have hO : IsOpen (latN F ι N : Set (ι → A F)) := by
    rw [latN_coe_eq_pi]
    exact isOpen_set_pi Set.finite_univ fun _ _ => hOpen N hN
  refine ⟨hC, hO, fun a => ?_⟩
  have hclopen : IsClopen (latN F ι N : Set (ι → A F)) := ⟨hC.isClosed, hO⟩
  have hcont : Continuous fun x : ι → A F => x - toA a := continuous_id.sub continuous_const
  have hS : IsClopen {x : ι → A F | x - toA a ∈ latN F ι N} := hclopen.preimage hcont
  have hK : IsCompact {x : ι → A F | x - toA a ∈ latN F ι N} := by
    have h : {x : ι → A F | x - toA a ∈ latN F ι N} =
        (fun x => x + toA a) '' (latN F ι N : Set (ι → A F)) := by
      ext x
      constructor
      · intro hx
        exact ⟨x - toA a, hx, by simp⟩
      · rintro ⟨y, hy, rfl⟩
        simpa using hy
    rw [h]
    exact hC.image (continuous_id.add continuous_const)
  refine ⟨?_, HasCompactSupport.of_support_subset_isCompact hK Set.support_indicator_subset⟩
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  by_cases hx : x ∈ {x : ι → A F | x - toA a ∈ latN F ι N}
  · filter_upwards [hS.isOpen.mem_nhds hx] with y hy
    have hy' : y ∈ {x : ι → A F | x - toA a ∈ latN F ι N} := hy
    rw [indC, Set.indicator_of_mem hx, Set.indicator_of_mem hy']
  · filter_upwards [hS.compl.isOpen.mem_nhds hx] with y hy
    have hy' : y ∉ {x : ι → A F | x - toA a ∈ latN F ι N} := hy
    rw [indC, Set.indicator_of_notMem hx, Set.indicator_of_notMem hy']

end GlobalTheory.CompanionTheory.SW.ThW.Lco
