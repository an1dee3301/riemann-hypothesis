module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagWZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerMemSchwartzBruhatFinitePlace
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Core
public import Init.Data.Function
public import Init.Data.Sum.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Invertible.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Invertible
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Prod
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Ker
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Module.Submodule.LinearMap
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Notation.Support
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Support
public import Mathlib.Topology.Closure
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels MeasureTheory GlobalTheory.LatVac GlobalTheory.InertVacLag GlobalTheory.InertLagChar
open scoped TensorProduct Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.InertLagChar.LinForm

theorem hasCompactSupport_comp_of_leftInverse {X Y M : Type} [TopologicalSpace X] [TopologicalSpace Y] [T2Space X]
    [Zero M] {f : X → Y} {l : Y → X} (hl : Continuous l) (hlf : ∀ x, l (f x) = x) {g : Y → M}
    (hg : HasCompactSupport g) : HasCompactSupport (g ∘ f) := by
  refine IsCompact.of_isClosed_subset (hg.image hl) isClosed_closure ?_
  refine closure_minimal ?_ (hg.image hl).isClosed
  intro x hx
  exact ⟨f x, subset_tsupport _ hx, hlf x⟩

theorem integrable_of_cont_cs {X : Type} [TopologicalSpace X] (μ : @Measure X (borel X))
    [IsFiniteMeasureOnCompacts μ] {f : X → ℂ} (hf : Continuous f) (hcs : HasCompactSupport f) :
    Integrable f μ := by
  letI : MeasurableSpace X := borel X
  haveI : BorelSpace X := ⟨rfl⟩
  exact hf.integrable_of_hasCompactSupport hcs

end GlobalTheory.InertLagChar.LinForm

open GlobalTheory.InertLagChar.LinForm in
theorem GlobalTheory.InertLagChar.lagInt_linForm : ∀ (F : Type) [Field F] [NumberField F] (v : Pl (F := F)) (κ : Type) [Fintype κ] (ψ : AddChar (Fv F v) ℂ), Continuous ψ →
    ∀ (μ : @Measure (κ → Fv F v) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∀ (N : ℕ) (ν : @Measure (Fin N → Fv F v) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) ν →
    ∀ j : (Fin N → Fv F v) →ₗ[Fv F v] (κ → Fv F v) × (κ → Fv F v), Function.Injective j →
    (∀ Φ ∈ SB (κ ⊕ κ → Fv F v), diagW ψ μ Φ ∈ SB ((κ → Fv F v) × (κ → Fv F v))) →
    ∃ Λ : ((κ ⊕ κ → Fv F v) → ℂ) →ₗ[ℂ] ℂ, ∀ Φ ∈ SB (κ ⊕ κ → Fv F v), Λ Φ = lagInt ψ μ ν j Φ := by
  intro F _ _ v κ _ ψ hψ μ hμ N ν hν j hj hdiag

  have hd : Continuous (fun x : κ → Fv F v => (Sum.elim x x : κ ⊕ κ → Fv F v)) := by
    refine continuous_pi fun i => ?_
    cases i <;> exact continuous_apply _
  have hdl : Continuous (fun z : κ ⊕ κ → Fv F v => fun i => z (Sum.inl i)) :=
    continuous_pi fun i => continuous_apply _

  have hin : ∀ w : (κ → Fv F v) × (κ → Fv F v), ∀ Φ ∈ SB (κ ⊕ κ → Fv F v),
      Integrable (fun x => schr ψ (Sum.elim w.1 0, Sum.elim w.2 0) Φ (Sum.elim x x)) μ := by
    intro w Φ hΦ
    have hs := GlobalTheory.SchrSBFin.schr_mem_SB v ψ hψ (Sum.elim w.1 0, Sum.elim w.2 0) Φ hΦ
    exact integrable_of_cont_cs μ (hs.1.continuous.comp hd)
      (hasCompactSupport_comp_of_leftInverse hdl (fun x => rfl) hs.2)
  have hschr_add : ∀ w (Φ Φ' : (κ ⊕ κ → Fv F v) → ℂ), schr ψ w (Φ + Φ') = schr ψ w Φ + schr ψ w Φ' := by
    intro w Φ Φ'; funext x; simp [schr, mul_add]
  have hschr_smul : ∀ w (c : ℂ) (Φ : (κ ⊕ κ → Fv F v) → ℂ), schr ψ w (c • Φ) = c • schr ψ w Φ := by
    intro w c Φ; funext x; simp [schr]; ring
  have hdiag_add : ∀ Φ ∈ SB (κ ⊕ κ → Fv F v), ∀ Φ' ∈ SB (κ ⊕ κ → Fv F v),
      diagW ψ μ (Φ + Φ') = diagW ψ μ Φ + diagW ψ μ Φ' := by
    intro Φ hΦ Φ' hΦ'
    funext w
    simp only [diagW, Pi.add_apply, hschr_add]
    exact integral_add (hin w Φ hΦ) (hin w Φ' hΦ')
  have hdiag_smul : ∀ (c : ℂ) (Φ : (κ ⊕ κ → Fv F v) → ℂ), diagW ψ μ (c • Φ) = c • diagW ψ μ Φ := by
    intro c Φ
    funext w
    simp only [diagW, Pi.smul_apply, hschr_smul, smul_eq_mul]
    exact integral_const_mul (μ := μ) c _

  obtain ⟨l, hl⟩ := LinearMap.exists_leftInverse_of_injective j (LinearMap.ker_eq_bot.mpr hj)
  have hjc : Continuous j := IsModuleTopology.continuous_of_linearMap j
  have hlc : Continuous l := IsModuleTopology.continuous_of_linearMap l
  have hlj : ∀ y, l (j y) = y := fun y => by
    have := LinearMap.congr_fun hl y
    simpa using this
  have hout : ∀ Φ ∈ SB (κ ⊕ κ → Fv F v), Integrable (fun y => diagW ψ μ Φ (j y)) ν := by
    intro Φ hΦ
    have hs := hdiag Φ hΦ
    have hcs : HasCompactSupport (diagW ψ μ Φ ∘ (j : (Fin N → Fv F v) → (κ → Fv F v) × (κ → Fv F v))) :=
      hasCompactSupport_comp_of_leftInverse (f := (j : (Fin N → Fv F v) → (κ → Fv F v) × (κ → Fv F v)))
        (l := (l : (κ → Fv F v) × (κ → Fv F v) → (Fin N → Fv F v))) hlc hlj hs.2
    have hc : Continuous (diagW ψ μ Φ ∘ (j : (Fin N → Fv F v) → (κ → Fv F v) × (κ → Fv F v))) :=
      hs.1.continuous.comp hjc
    exact integrable_of_cont_cs ν hc hcs
  let f : SB (κ ⊕ κ → Fv F v) →ₗ[ℂ] ℂ :=
    { toFun := fun Φ => lagInt ψ μ ν j Φ.1
      map_add' := by
        intro Φ Φ'
        simp only [Submodule.coe_add, lagInt, hdiag_add _ Φ.2 _ Φ'.2, Pi.add_apply]
        exact integral_add (hout _ Φ.2) (hout _ Φ'.2)
      map_smul' := by
        intro c Φ
        simp only [Submodule.coe_smul, lagInt, hdiag_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        exact integral_const_mul (μ := ν) c _ }
  obtain ⟨g, hg⟩ := LinearMap.exists_extend f
  exact ⟨g, fun Φ hΦ => LinearMap.congr_fun hg ⟨Φ, hΦ⟩⟩
