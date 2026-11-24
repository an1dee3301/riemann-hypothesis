module

public import Mathlib
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsVecFixGroup
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsComplementForm
public import Development.Core20Slim.GroundTheory.AutomorphicForms.HermitianSpaces
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Objects
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.SecondCountableTopologyArchUnitary
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.PropLemmas
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Pi
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.GroupTheory.Index
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.LinearAlgebra.InvariantBasisNumber
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.SetNotation
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Basic
public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix Topology MeasureTheory
open scoped ENNReal

noncomputable section

section Radical

variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable [NumberField E]

def unipRadical (h : HermitianForm F E W) (v : Basis ι E W) (x₀ : W) :
    Subgroup (archUnitary h v) where
  carrier := {g | ∀ w, ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ vecAt v x₀ w =
    vecAt v x₀ w ∧ ∀ z : ι → ℂ, star (vecAt v x₀ w) ⬝ᵥ (gramAt h v w *ᵥ z) = 0 →
      ∃ c : ℂ, ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ z = z + c • vecAt v x₀ w}
  one_mem' w := ⟨by simp, fun z _ => ⟨0, by simp⟩⟩
  mul_mem' {a b} ha hb w := by
    refine ⟨?_, fun z hz => ?_⟩
    · simp only [Subgroup.coe_mul, Pi.mul_apply, Units.val_mul, ← Matrix.mulVec_mulVec, (hb w).1,
        (ha w).1]
    · obtain ⟨c, hc⟩ := (hb w).2 z hz
      obtain ⟨d, hd⟩ := (ha w).2 z hz
      refine ⟨d + c, ?_⟩
      simp only [Subgroup.coe_mul, Pi.mul_apply, Units.val_mul, ← Matrix.mulVec_mulVec, hc,
        Matrix.mulVec_add, Matrix.mulVec_smul, hd, (ha w).1, add_smul]
      abel
  inv_mem' {a} ha w := by
    have e : (((a⁻¹ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *
        ((a : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) = 1 := by
      rw [Subgroup.coe_inv, Pi.inv_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one]
    have hx : (((a⁻¹ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ
        vecAt v x₀ w = vecAt v x₀ w := by
      conv_lhs => rw [← (ha w).1]
      rw [Matrix.mulVec_mulVec, e, Matrix.one_mulVec]
    refine ⟨hx, fun z hz => ?_⟩
    obtain ⟨c, hc⟩ := (ha w).2 z hz
    refine ⟨-c, ?_⟩
    have := congrArg ((((a⁻¹ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ ·) hc
    simp only [Matrix.mulVec_mulVec, e, Matrix.one_mulVec, Matrix.mulVec_add, Matrix.mulVec_smul,
      hx] at this
    rw [neg_smul, ← sub_eq_add_neg, eq_sub_iff_add_eq, ← this]

omit [NumberField E] in
theorem mem_unipRadical {h : HermitianForm F E W} {v : Basis ι E W} {x₀ : W}
    {g : archUnitary h v} : g ∈ unipRadical h v x₀ ↔
      ∀ w, ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ vecAt v x₀ w = vecAt v x₀ w ∧
        ∀ z : ι → ℂ, star (vecAt v x₀ w) ⬝ᵥ (gramAt h v w *ᵥ z) = 0 →
          ∃ c : ℂ, ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ z = z + c • vecAt v x₀ w :=
  Iff.rfl


omit [NumberField E] in
theorem unipRadical_le_vecFixGroup (h : HermitianForm F E W) (v : Basis ι E W) (x₀ : W) :
    unipRadical h v x₀ ≤ vecFixGroup h v x₀ :=
  fun _ hg w => (hg w).1


omit [NumberField E] in
theorem isClosed_unipRadical (h : HermitianForm F E W) (v : Basis ι E W) (x₀ : W) :
    IsClosed (unipRadical h v x₀ : Set (archUnitary h v)) := by
  have hc : ∀ w, Continuous fun g : archUnitary h v =>
      ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) :=
    fun w => Units.continuous_val.comp ((continuous_apply w).comp continuous_subtype_val)
  have : (unipRadical h v x₀ : Set (archUnitary h v)) = ⋂ w, ({g : archUnitary h v |
      ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ vecAt v x₀ w = vecAt v x₀ w} ∩
      ⋂ z ∈ {z : ι → ℂ | star (vecAt v x₀ w) ⬝ᵥ (gramAt h v w *ᵥ z) = 0},
        (fun g : archUnitary h v => ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ z - z) ⁻¹'
          (Submodule.span ℂ {vecAt v x₀ w} : Set (ι → ℂ))) := by
    ext g
    simp only [SetLike.mem_coe, mem_unipRadical, Set.mem_iInter, Set.mem_inter_iff,
      Set.mem_ofPred_eq, Set.mem_preimage, Submodule.mem_span_singleton]
    refine forall_congr' fun w => and_congr Iff.rfl (forall_congr' fun z => imp_congr_right
      fun _ => ⟨fun ⟨c, hc⟩ => ⟨c, by rw [hc]; abel⟩, fun ⟨c, hc⟩ => ⟨c, by rw [hc]; abel⟩⟩)
  rw [this]
  refine isClosed_iInter fun w => (isClosed_eq ((hc w).matrix_mulVec continuous_const)
    continuous_const).inter (isClosed_biInter fun z _ => ?_)
  exact (Submodule.closed_of_finiteDimensional _).preimage
    (((hc w).matrix_mulVec continuous_const).sub continuous_const)

instance locallyCompactSpace_unipRadical (h : HermitianForm F E W) (v : Basis ι E W) (x₀ : W) :
    LocallyCompactSpace (unipRadical h v x₀) :=
  (isClosed_unipRadical h v x₀).isClosedEmbedding_subtypeVal.locallyCompactSpace

instance secondCountableTopology_unipRadical (h : HermitianForm F E W) (v : Basis ι E W)
    (x₀ : W) : SecondCountableTopology (unipRadical h v x₀) :=
  TopologicalSpace.Subtype.secondCountableTopology _

end Radical

section Structure

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

def StabilizerLevi.Statement (h : HermitianForm F E W) (v : Basis ι E W) : Prop :=
  ∀ x₀ w₀ : W, IsHyperbolicPair h x₀ w₀ → ∀ h' : HermitianForm F E (hypComplement h x₀ w₀),
    (∀ x y, h'.toSesq x y = h.toSesq x y) →
    ∀ (n : ℕ) (v' : Basis (Fin n) E (hypComplement h x₀ w₀)),
    ∃ (i : archUnitary h' v' →* vecFixGroup h v x₀) (q : vecFixGroup h v x₀ →* archUnitary h' v'),
      Continuous i ∧ Continuous q ∧ (∀ m, q (i m) = m) ∧
      (∀ g, q g = 1 ↔ (g : archUnitary h v) ∈ unipRadical h v x₀) ∧
      (∀ m, ((i m : vecFixGroup h v x₀) : archUnitary h v) ∈ vecFixGroup h v w₀) ∧
      ∀ (γ : h.unitaryGroup) (m : h'.unitaryGroup), γ • x₀ = x₀ → γ • w₀ = w₀ →
        (∀ x : hypComplement h x₀ w₀, γ • (x : W) = ((m • x : hypComplement h x₀ w₀) : W)) →
        ((i (archEmbed h' v' m) : vecFixGroup h v x₀) : archUnitary h v) = archEmbed h v γ

def UnipotentModulus.Statement (h : HermitianForm F E W) (v : Basis ι E W) : Prop :=
  ∀ x₀ w₀ : W, IsHyperbolicPair h x₀ w₀ →
    ∀ (μ : Measure (unipRadical h v x₀)) [μ.IsHaarMeasure],
    ∀ g ∈ vecFixGroup h v x₀ ⊓ vecFixGroup h v w₀,
      μ.map (fun n : unipRadical h v x₀ => g * (n : archUnitary h v) * g⁻¹) = μ.map Subtype.val

def UnipotentCocompact.Statement (h : HermitianForm F E W) (v : Basis ι E W) : Prop :=
  ∀ (D : ℕ) (La : AddSubgroup W) (x₀ : W), IsDIntegral h D La → x₀ ∈ La → x₀ ≠ 0 →
    h.toSesq x₀ x₀ = 0 →
    ∃ C : Set (unipRadical h v x₀), IsCompact C ∧ ∀ n : unipRadical h v x₀,
      ∃ δ : unipRadical h v x₀, (δ : archUnitary h v) ∈ vecStabGroup h v La x₀ ∧ δ * n ∈ C

def CongruenceLift.Statement [FiniteDimensional E W] (h : HermitianForm F E W) : Prop :=
  ∀ (D : ℕ) (La : AddSubgroup W) (x₀ w₀ : W), IsDIntegral h D La → x₀ ∈ La →
    IsHyperbolicPair h x₀ w₀ → ∀ h' : HermitianForm F E (hypComplement h x₀ w₀),
    (∀ x y, h'.toSesq x y = h.toSesq x y) →
    ∃ (D' : ℕ) (La' : AddSubgroup (hypComplement h x₀ w₀)) (G'' : Subgroup h'.unitaryGroup),
      IsDIntegral h' D' La' ∧ G'' ≤ latticeStab h' La' ∧ G''.relIndex (latticeStab h' La') ≠ 0 ∧
      ∀ m ∈ G'', ∀ γ : h.unitaryGroup, γ • x₀ = x₀ → γ • w₀ = w₀ →
        (∀ x : hypComplement h x₀ w₀, γ • (x : W) = ((m • x : hypComplement h x₀ w₀) : W)) →
        γ ∈ latticeStab h La

end Structure

section Inhabitants

open GaussianPlane

end Inhabitants

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
