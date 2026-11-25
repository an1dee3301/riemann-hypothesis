module

public import Development.Core20Slim.Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.RightOnto
public import Development.Core20Slim.Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.TopOfMap
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OmegaEquivInducedFibreStatement
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.OpenClosedSequences
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Development.AbelianVarietyTheory.Definitions.Foundations.SecondCountableAndT2LocalField
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.RankFiltrationExists
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibRepApply
public import Init.Classical
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Module.Submodule.Map
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Torsor.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Insert
public import Mathlib.Data.Set.Operations
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.Order.Basic
public import Mathlib.Order.BoundedOrder.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Filter.Map
public import Mathlib.Order.Notation
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.RepresentationTheory.Intertwining
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
public import Mathlib.Topology.Algebra.Group.Torsor
public import Mathlib.Topology.Algebra.Support
public import Mathlib.Topology.Algebra.ValuativeRel.ValuativeTopology
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Basic
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Topology.Maps.Basic
public import Mathlib.Topology.Neighborhoods
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.Separation.Regular

@[expose] public section

noncomputable section

namespace PositivityTheory.KCo

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences GlobalTheory.RankStrataProof GlobalTheory.CompanionTheory.ThetaGLLen Matrix Topology GlobalTheory.SplitFlip

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n d : ℕ}


open Classical in
def extZ : SB (RankIn k (Fin n) (Fin d) {n}) →ₗ[ℂ] (Matrix (Fin n) (Fin d) k → ℂ) where
  toFun φ Y := if h : Yᵀ.rank = n then φ.1 ⟨Yᵀ, h⟩ else 0
  map_add' φ ψ := funext fun Y => by by_cases h : Yᵀ.rank = n <;> simp [h, -rank_transpose]
  map_smul' c φ := funext fun Y => by by_cases h : Yᵀ.rank = n <;> simp [h, -rank_transpose]

theorem extZ_pos (φ : SB (RankIn k (Fin n) (Fin d) {n})) {Y : Matrix (Fin n) (Fin d) k} (h : Yᵀ.rank = n) :
    extZ φ Y = φ.1 ⟨Yᵀ, h⟩ := dif_pos h

theorem extZ_neg (φ : SB (RankIn k (Fin n) (Fin d) {n})) {Y : Matrix (Fin n) (Fin d) k} (h : Yᵀ.rank ≠ n) :
    extZ φ Y = 0 := dif_neg h

theorem isOpenEmb : IsOpenEmbedding fun x : RankIn k (Fin n) (Fin d) {n} => x.1ᵀ := by
  have hXo : IsOpen {x : Matrix (Fin d) (Fin n) k | x.rank ∈ ({n} : Set ℕ)} := by
    convert isOpen_le_rank (k := k) (a := Fin n) (b := Fin d) n using 1
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    exact ⟨fun h => h.ge, fun h => le_antisymm (Matrix.rank_le_width x) h⟩
  let T : Matrix (Fin d) (Fin n) k ≃ₜ Matrix (Fin n) (Fin d) k :=
    { toFun := transpose, invFun := transpose, left_inv := fun _ => rfl, right_inv := fun _ => rfl,
      continuous_toFun := continuous_id.matrix_transpose, continuous_invFun := continuous_id.matrix_transpose }
  exact T.isOpenEmbedding.comp hXo.isOpenEmbedding_subtypeVal

theorem extZ_mem (φ : SB (RankIn k (Fin n) (Fin d) {n})) : extZ φ ∈ SB (Matrix (Fin n) (Fin d) k) := by
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  have hi := isOpenEmb (k := k) (n := n) (d := d)
  have hC : IsCompact ((fun x : RankIn k (Fin n) (Fin d) {n} => x.1ᵀ) '' tsupport φ.1) := φ.2.2.image hi.continuous
  have h0 : ∀ Y ∉ (fun x : RankIn k (Fin n) (Fin d) {n} => x.1ᵀ) '' tsupport φ.1, extZ φ Y = 0 := fun Y hY => by
    by_cases h : Yᵀ.rank = n
    · rw [extZ_pos φ h]
      exact image_eq_zero_of_notMem_tsupport fun hm => hY ⟨_, hm, rfl⟩
    · exact extZ_neg φ h
  refine ⟨(IsLocallyConstant.iff_eventually_eq _).2 fun Y => ?_, HasCompactSupport.intro hC h0⟩
  by_cases h : Yᵀ.rank = n
  · have e := hi.map_nhds_eq ⟨Yᵀ, h⟩
    rw [transpose_transpose] at e
    rw [← e, Filter.eventually_map, extZ_pos φ h]
    filter_upwards [(IsLocallyConstant.iff_eventually_eq _).1 φ.2.1 ⟨Yᵀ, h⟩] with x hx
    rw [extZ_pos φ (Y := x.1ᵀ) x.2]
    exact hx
  · have hY : Y ∉ (fun x : RankIn k (Fin n) (Fin d) {n} => x.1ᵀ) '' tsupport φ.1 := by
      rintro ⟨x, -, rfl⟩
      exact h x.2
    filter_upwards [hC.isClosed.isOpen_compl.mem_nhds hY] with Z hZ
    rw [h0 Z hZ, h0 Y hY]

theorem exists_extZ {Φ : Matrix (Fin n) (Fin d) k → ℂ} (h : Full Φ) : ∃ φ, extZ φ = Φ := by
  refine ⟨⟨_, comp_mem_SB_of_isInducing (isOpenEmb (k := k) (n := n) (d := d)).isInducing ⟨Φ, h.1⟩ isClosed_univ (fun _ => trivial)
    fun Y _ hY => ⟨⟨Yᵀ, (rank_transpose Y).trans (not_not.1 fun e => hY (h.2 Y e))⟩, rfl⟩⟩, funext fun Y => ?_⟩
  by_cases hY : Yᵀ.rank = n
  · exact extZ_pos _ hY
  · rw [extZ_neg _ hY, h.2 Y (by rwa [rank_transpose] at hY)]

theorem extZ_act (μ : kˣ →* ℂˣ) (g : GL (Fin n) k) (h : GL (Fin d) k) (φ : SB (RankIn k (Fin n) (Fin d) {n}))
    (Y : Matrix (Fin n) (Fin d) k) : extZ (omegaOn (Fin n) (Fin d) μ {n} (g, h) φ) Y =
      (omChar (Fin n) (Fin d) μ (g, h) : ℂ) * extZ φ (g.valᵀ * Y * (invT h).val) := by
  have e : (g.valᵀ * Y * (invT h).val)ᵀ = act Yᵀ (g, h) := by
    simp only [act, invT, transpose_mul, MonoidHom.coe_mk, OneHom.coe_mk, transpose_transpose, Matrix.mul_assoc]
  by_cases hY : Yᵀ.rank = n
  · rw [extZ_pos _ hY, extZ_pos φ (by rw [e, rank_act]; exact hY)]
    exact congrArg (fun x => (omChar (Fin n) (Fin d) μ (g, h) : ℂ) * φ.1 x) (Subtype.ext e.symm)
  · rw [extZ_neg _ hY, extZ_neg φ (by rw [e, rank_act]; exact hY), mul_zero]

theorem irr_equiv {Γ G V U : Type} [Group Γ] [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup U] [Module ℂ U]
    {τ : Representation ℂ (Γ × G) V} {τ' : Representation ℂ (Γ × G) U} (E : τ.Equiv τ')
    (H : ∀ N : Submodule ℂ U, twRel (τ'.comp (MonoidHom.inl _ _)) 1 ≤ N → (∀ h, ∀ f ∈ N, τ' (1, h) f ∈ N) →
      N = ⊤ ∨ N ≤ twRel (τ'.comp (MonoidHom.inl _ _)) 1)
    (N : Submodule ℂ V) (hR : twRel (τ.comp (MonoidHom.inl _ _)) 1 ≤ N) (hN : ∀ h, ∀ f ∈ N, τ (1, h) f ∈ N) :
    N = ⊤ ∨ N ≤ twRel (τ.comp (MonoidHom.inl _ _)) 1 := by
  have hE : ∀ γ φ, E.toLinearEquiv (τ γ φ) = τ' γ (E.toLinearEquiv φ) := fun γ φ => LinearMap.congr_fun (E.isIntertwining' γ) φ
  have h1 : twRel (τ'.comp (MonoidHom.inl _ _)) 1 ≤ (twRel (τ.comp (MonoidHom.inl _ _)) 1).map E.toLinearEquiv.toLinearMap :=
    Submodule.span_le.2 (by
      rintro _ ⟨g, f, rfl⟩
      obtain ⟨φ, rfl⟩ := E.toLinearEquiv.surjective f
      exact ⟨_, Submodule.subset_span ⟨g, φ, rfl⟩, by rw [map_sub, map_smul]; exact congrArg (· - _) (hE (g, 1) φ)⟩)
  rcases H (N.map E.toLinearEquiv.toLinearMap) (h1.trans (Submodule.map_mono hR)) (by
    rintro h _ ⟨f, hf, rfl⟩
    exact ⟨_, hN h f hf, hE _ f⟩) with h | h
  · exact Or.inl (top_of_map E.toLinearEquiv.toLinearMap (R := ⊥) (fun f hf => E.toLinearEquiv.map_eq_zero_iff.1 hf) bot_le h)
  · refine Or.inr fun f hf => ?_
    obtain ⟨g, hg, e⟩ := h1 (h ⟨f, hf, rfl⟩)
    rwa [← E.toLinearEquiv.injective e]

end PositivityTheory.KCo
