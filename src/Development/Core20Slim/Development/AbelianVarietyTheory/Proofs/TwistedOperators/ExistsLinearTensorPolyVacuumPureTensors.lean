module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaSubSelf
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HypothesesAbsDet
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.AlgAtLeAlgD
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaTransformGaussianVacuumIsFiniteDatum
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.ByCases
public import Init.Classical
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.PropLemmas
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.IsApply
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.LinearMap
public import Mathlib.Algebra.Module.Submodule.Range
public import Mathlib.Algebra.Notation.Indicator
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Notation.Support
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Basic.Finite.Prod
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Attach
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sets
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Finite.Lattice
public import Mathlib.Data.Set.Operations
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.Multilinear.Basic
public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.Cofinite
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.SetNotation
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open NumberField IsDedekindDomain
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.HoweGlobal.TensorMap

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F : Type} [Field F] [NumberField F]

theorem finite_nonint {κ : Type} [Finite κ] (x : κ → AF F) :
    {w : Pl F | ¬ ∀ i, evFin F w (x i) ∈ w.adicCompletionIntegers F}.Finite := by
  have h : ∀ i, {w : Pl F | evFin F w (x i) ∉ w.adicCompletionIntegers F}.Finite := fun i =>
    Filter.eventually_cofinite.1 (x i).2.2
  refine (Set.finite_iUnion h).subset ?_
  intro w hw
  push_neg at hw
  obtain ⟨i, hi⟩ := hw
  exact Set.mem_iUnion.2 ⟨i, hi⟩

variable {E : Type} [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
  {Y : Spc F E n} {W : Spc F E d}


open Classical in
def vacOff (M : Model σ Y W) (T : Finset (Pl F)) (x : Fin n × Fin d → AF F) : ℂ :=
  ∏ᶠ w, if w ∈ T then (1 : ℂ) else M.vac w fun i => evFin F w (x i)

def prodT (T : Finset (Pl F)) (x : Fin n × Fin d → AF F) :
    (Π v : T, ↥(SB (Fin n × Fin d → Fv F v.1))) →ₘₗ[ℂ] ℂ :=
  (MultilinearMap.mkPiAlgebra ℂ T ℂ).compLinearMap fun v =>
    (LinearMap.proj (fun i => evFin F v.1 (x i)) : ((Fin n × Fin d → Fv F v.1) → ℂ) →ₗ[ℂ] ℂ) ∘ₗ (SB _).subtype

theorem prodT_apply (T : Finset (Pl F)) (x : Fin n × Fin d → AF F) (φ : ∀ v : T, ↥(SB (Fin n × Fin d → Fv F v.1))) :
    prodT T x φ = ∏ v : T, (φ v : (Fin n × Fin d → Fv F v.1) → ℂ) fun i => evFin F v.1 (x i) := by
  simp [prodT]

def multi (M : Model σ Y W) (T : Finset (Pl F)) (f : SInf F (Fin n × Fin d)) :
    (Π v : T, ↥(SB (Fin n × Fin d → Fv F v.1))) →ₘₗ[ℂ] ((Fin n × Fin d → AF F) → ℂ) :=
  MultilinearMap.pi fun x => (f (fun i => evI F (x i)) * vacOff M T x) • prodT T x

theorem multi_apply (M : Model σ Y W) (T : Finset (Pl F)) (f : SInf F (Fin n × Fin d))
    (φ : ∀ v : T, ↥(SB (Fin n × Fin d → Fv F v.1))) (x : Fin n × Fin d → AF F) :
    multi M T f φ x = f (fun i => evI F (x i)) * vacOff M T x * prodT T x φ := by
  simp [multi]

def multiL (M : Model σ Y W) (T : Finset (Pl F)) :
    SInf F (Fin n × Fin d) →ₗ[ℂ]
      ((Π v : T, ↥(SB (Fin n × Fin d → Fv F v.1))) →ₘₗ[ℂ] ((Fin n × Fin d → AF F) → ℂ)) where
  toFun := multi M T
  map_add' f g := by
    ext φ x
    simp only [multi_apply, MultilinearMap.add_apply, Pi.add_apply, SchwartzMap.add_apply]
    ring
  map_smul' c f := by
    ext φ x
    simp only [multi_apply, MultilinearMap.smul_apply, Pi.smul_apply, SchwartzMap.smul_apply, smul_eq_mul,
      RingHom.id_apply]
    ring


open Classical in
theorem finprod_split (M : Model σ Y W)
    (hstd : ∀ᶠ v in Filter.cofinite, M.vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1)
    (T : Finset (Pl F)) (φ : ∀ v : T, ↥(SB (Fin n × Fin d → Fv F v.1)))
    (φ' : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ)
    (h1 : ∀ v (h : v ∈ T), φ' v = φ ⟨v, h⟩) (h2 : ∀ v ∉ T, φ' v = M.vac v) (x : Fin n × Fin d → AF F) :
    ∏ᶠ w, φ' w (fun i => evFin F w (x i)) = vacOff M T x * prodT T x φ := by
  set ρ : Pl F → ℂ := fun w => if w ∈ T then (1 : ℂ) else M.vac w fun i => evFin F w (x i) with hρdef
  set θ : Pl F → ℂ := fun w => if w ∈ T then φ' w (fun i => evFin F w (x i)) else 1 with hθdef
  have e : (fun w => φ' w (fun i => evFin F w (x i))) = fun w => θ w * ρ w := by
    funext w
    by_cases hw : w ∈ T
    · simp [θ, ρ, hw]
    · simp [θ, ρ, hw, h2 w hw]
  have hρ : (Function.mulSupport ρ).Finite := by
    refine ((Filter.eventually_cofinite.1 hstd).union (finite_nonint x)).subset ?_
    intro w hw
    by_contra hc
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hc
    apply hw
    by_cases hwT : w ∈ T
    · simp [ρ, hwT]
    · simp only [ρ, hwT, if_false, hc.1]
      exact Set.indicator_of_mem (s := {x : Fin n × Fin d → Fv F w | ∀ i, x i ∈ w.adicCompletionIntegers F}) hc.2 1
  have hθ : Function.mulSupport θ ⊆ (T : Set (Pl F)) := by
    intro w hw
    by_contra hc
    exact hw (by simp [θ, show w ∉ T from hc])
  rw [e, finprod_mul_distrib (T.finite_toSet.subset hθ) hρ, mul_comm]
  congr 1
  rw [finprod_eq_prod_of_mulSupport_subset θ hθ, prodT_apply, ← Finset.prod_coe_sort T]
  refine Finset.prod_congr rfl fun v _ => ?_
  simp [θ, v.2, h1 v.1 v.2]

def tensL (M : Model σ Y W) (ψ : AddChar (AF F) ℂ) (emb : ∀ w : InfinitePlace F, EmbOver E w) (T : Finset (Pl F)) :
    ↥(M.Pol ψ emb) ⊗[ℂ] (⨂[ℂ] v : T, ↥(SB (Fin n × Fin d → Fv F v.1))) →ₗ[ℂ]
      ((Fin n × Fin d → AF F) → ℂ) :=
  TensorProduct.lift ((PiTensorProduct.lift.toLinearMap ∘ₗ multiL M T) ∘ₗ (M.Pol ψ emb).subtype)

theorem tensL_tmul (M : Model σ Y W) (ψ : AddChar (AF F) ℂ) (emb : ∀ w : InfinitePlace F, EmbOver E w)
    (T : Finset (Pl F)) (f : ↥(M.Pol ψ emb)) (φ : ∀ v : T, ↥(SB (Fin n × Fin d → Fv F v.1))) :
    tensL M ψ emb T (f ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ φ) = multi M T (f : SInf F (Fin n × Fin d)) φ := by
  simp [tensL, multiL]

theorem exists_tensL : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y W)
    (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) ℂ) (emb : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w),
    (∀ᶠ v in Filter.cofinite, M.vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) →
    ∀ T : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)),
    ∃ L : ↥(M.Pol ψ emb) ⊗[ℂ] (⨂[ℂ] v : T, ↥(GlobalTheory.WeilM.SB (Fin n × Fin d → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v.1))) →ₗ[ℂ]
        ((Fin n × Fin d → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) → ℂ),
      (∀ (f : ↥(M.Pol ψ emb)) (φ : ∀ v : T, ↥(GlobalTheory.WeilM.SB (Fin n × Fin d → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v.1)))
        (φ' : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin n × Fin d → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ),
        (∀ v (h : v ∈ T), φ' v = φ ⟨v, h⟩) → (∀ v ∉ T, φ' v = M.vac v) →
        L (f ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)) φ') ∧
      GlobalTheory.HoweGlobal.algAt M ψ emb T ≤ LinearMap.range L := by
  intro F E _ _ _ _ _ σ n d Y W M ψ emb hstd T
  have hchar : ∀ (f : ↥(M.Pol ψ emb)) (φ : ∀ v : T, ↥(SB (Fin n × Fin d → Fv F v.1)))
      (φ' : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ),
      (∀ v (h : v ∈ T), φ' v = φ ⟨v, h⟩) → (∀ v ∉ T, φ' v = M.vac v) →
      tensL M ψ emb T (f ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f : SInf F (Fin n × Fin d)) φ' := by
    intro f φ φ' h1 h2
    funext x
    rw [tensL_tmul, multi_apply, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, finprod_split M hstd T φ φ' h1 h2 x, mul_assoc]
  refine ⟨tensL M ψ emb T, hchar, Submodule.span_le.2 ?_⟩
  rintro Φ ⟨f, φ, hf, hφ, hv, rfl⟩
  exact ⟨⟨f, hf⟩ ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ (fun v : T => ⟨φ v.1, hφ v.1⟩),
    hchar ⟨f, hf⟩ _ φ (fun _ _ => rfl) hv⟩

end GlobalTheory.HoweGlobal.TensorMap
