module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ArchActOne
public import Development.Core20Slim.GroundTheory.GlobalFields.Adele.Compact
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPairingStdP
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import GroundTheory.GlobalFields.Adele.Approximation
public import Init.Classical
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.WithOne.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Indicator
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Pi
public import Mathlib.Algebra.Ring.Prod
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
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
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sets
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Operations
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace
public import Mathlib.Topology.Algebra.Support
public import Mathlib.Topology.Algebra.Valued.ValuationTopology
public import Mathlib.Topology.Clopen
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.LocallyConstant.Algebra
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.ArchUniq GlobalTheory.ArchUniq.Coord GlobalTheory.ArchLine
open scoped Matrix Classical SchwartzMap

noncomputable section

namespace GlobalTheory.ArchLine.Laws

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d : ℕ} {X : Spc F E n} {W : Spc F E d}

def intInd (κ : Type) : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ :=
  (Set.pi Set.univ fun _ : κ => (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F : Set (FiniteAdeleRing (𝓞 F) F))).indicator 1

theorem intInd_mem (κ : Type) [Fintype κ] :
    intInd (F := F) κ ∈ SB (κ → FiniteAdeleRing (𝓞 F) F) := by
  have hOo : IsOpen (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F : Set (FiniteAdeleRing (𝓞 F) F)) := by
    unfold GroundTheory.Global.integralFiniteAdeles
    exact RestrictedProduct.isOpen_forall_mem (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
      (fun v => Valued.isOpen_valuationSubring (v.adicCompletion F))
  have hOc : IsCompact (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F : Set (FiniteAdeleRing (𝓞 F) F)) :=
    GroundTheory.Global.isCompact_integralFiniteAdeles F
  have hOcl : IsClosed (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F : Set (FiniteAdeleRing (𝓞 F) F)) :=
    hOc.isClosed
  have hU : IsClopen (Set.pi Set.univ fun _ : κ =>
      (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F : Set (FiniteAdeleRing (𝓞 F) F))) :=
    ⟨isClosed_set_pi fun _ _ => hOcl, isOpen_set_pi Set.finite_univ fun _ _ => hOo⟩
  show IsLocallyConstant (intInd (F := F) κ) ∧ HasCompactSupport (intInd (F := F) κ)
  refine ⟨(LocallyConstant.indicator (1 : LocallyConstant (κ → FiniteAdeleRing (𝓞 F) F) ℂ) hU).isLocallyConstant, ?_⟩
  exact HasCompactSupport.intro' (isCompact_univ_pi fun _ => hOc) hU.isClosed
    fun x hx => Set.indicator_of_notMem hx _

theorem snd_eq_zero_of_at {κ : Type} {z : κ → AF F} (hz : At (evI F) z) (i : κ) : (z i).2 = 0 := by
  let u : AF F := ((0 : InfiniteAdeleRing F), (1 : FiniteAdeleRing (𝓞 F) F))
  have hu : evI F u = 0 := map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)
  have h0 : u * z i = 0 := congrFun (hz u hu) i
  have h1 : (u * z i).2 = (1 : FiniteAdeleRing (𝓞 F) F) * (z i).2 := rfl
  rw [h0, one_mul] at h1
  exact h1.symm

def refFun (κ : Type) : (κ → AF F) → ℂ := fun x => intInd κ (fun i => (x i).2)

theorem refFun_rest {κ : Type} [Fintype κ] (f : SInf F κ) :
    Rest (evI F) (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (refFun κ) := by
  refine ⟨fun x z hz => ?_, Submodule.subset_span ⟨f, intInd κ, intInd_mem κ, rfl⟩⟩
  show intInd κ (fun i => (x i + z i).2) = intInd κ (fun i => (x i).2)
  congr 1
  funext i
  change (x i).2 + (z i).2 = (x i).2
  rw [snd_eq_zero_of_at hz i, add_zero]

theorem refFun_lift {κ : Type} (t : κ → mixedEmbedding.mixedSpace F) : refFun κ (liftV t) = 1 := by
  show intInd κ (fun i => (liftV t i).2) = 1
  unfold intInd
  rw [Set.indicator_of_mem]
  · rfl
  · intro i _
    change (0 : FiniteAdeleRing (𝓞 F) F) ∈ (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F : Set (FiniteAdeleRing (𝓞 F) F))
    exact zero_mem _

theorem tens_lift {κ : Type} (φ : (κ → mixedEmbedding.mixedSpace F) → ℂ) (t : κ → mixedEmbedding.mixedSpace F) :
    tens (evI F) φ (refFun κ) (liftV t) = φ t := by
  show φ (fun i => evI F (liftV t i)) * refFun κ (liftV t) = φ t
  rw [refFun_lift, mul_one]
  congr 1
  funext i
  exact RingEquiv.apply_symm_apply _ _

theorem eq_of_tens {κ : Type} [Fintype κ] {f₁ f₂ : SInf F κ}
    (h : tens (evI F) (f₁ : (κ → mixedEmbedding.mixedSpace F) → ℂ) (refFun κ) = tens (evI F) (f₂ : _ → ℂ) (refFun κ)) :
    f₁ = f₂ := by
  ext t
  have key := congrFun h (liftV t)
  rwa [tens_lift, tens_lift] at key

theorem tens_add {κ : Type} [Fintype κ] (f f' : SInf F κ) (r : (κ → AF F) → ℂ) :
    tens (evI F) (⇑(f + f') : (κ → mixedEmbedding.mixedSpace F) → ℂ) r = tens (evI F) ⇑f r + tens (evI F) ⇑f' r := by
  funext x
  change (f + f') (fun i => evI F (x i)) * r x = f (fun i => evI F (x i)) * r x + f' (fun i => evI F (x i)) * r x
  rw [SchwartzMap.add_apply, add_mul]

theorem tens_smul {κ : Type} [Fintype κ] (c : ℂ) (f : SInf F κ) (r : (κ → AF F) → ℂ) :
    tens (evI F) (⇑(c • f) : (κ → mixedEmbedding.mixedSpace F) → ℂ) r = c • tens (evI F) ⇑f r := by
  funext x
  change (c • f) (fun i => evI F (x i)) * r x = c • (f (fun i => evI F (x i)) * r x)
  rw [SchwartzMap.smul_apply, smul_mul_assoc]

theorem img (om : Rep σ X W) (h : UA σ W.J) (f : SInf F (Fin n × Fin d))
    (hx : ∃ f₁ : SInf F (Fin n × Fin d), Acts (evI F) (om (1, h)) ⇑f ⇑f₁) :
    om (1, h) (tens (evI F) ⇑f (refFun _)) = tens (evI F) ⇑(archOp om h f) (refFun _) := acts_archOp om h f hx _ (refFun_rest f)

theorem archOp_eq_of_acts (om : Rep σ X W) (h : UA σ W.J) (f f₁ : SInf F (Fin n × Fin d))
    (hA : Acts (evI F) (om (1, h)) ⇑f ⇑f₁) : archOp om h f = f₁ := by
  apply eq_of_tens
  rw [← img om h f ⟨f₁, hA⟩]
  exact hA _ (refFun_rest f)

end GlobalTheory.ArchLine.Laws

namespace GlobalTheory.ArchLine


open GlobalTheory.ArchLine.Laws in
theorem archOp_laws : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
    M.IsWeil ψ χX χW om → (∀ h ∈ UAt σ W (evI F), ∀ f : SInf F (Fin n × Fin d), ∃ f₁ : SInf F (Fin n × Fin d),
      Acts (evI F) (om (1, h)) ⇑f ⇑f₁) →
    (∀ h ∈ UAt σ W (evI F), ∀ f f' : SInf F (Fin n × Fin d), archOp om h (f + f') = archOp om h f + archOp om h f') ∧
    (∀ h ∈ UAt σ W (evI F), ∀ (c : ℂ) (f : SInf F (Fin n × Fin d)), archOp om h (c • f) = c • archOp om h f) ∧
    (∀ f : SInf F (Fin n × Fin d), archOp om 1 f = f) ∧
    (∀ h ∈ UAt σ W (evI F), ∀ h' ∈ UAt σ W (evI F), ∀ f : SInf F (Fin n × Fin d),
      archOp om (h * h') f = archOp om h (archOp om h' f)) := by
  intro F E _ _ _ _ _ σ n d X W M ψ χX χW om _ hex
  refine ⟨fun h hh f f' => ?_, fun h hh c f => ?_, fun f => ?_, fun h hh h' hh' f => ?_⟩
  · apply eq_of_tens
    rw [tens_add, ← img om h (f + f') (hex h hh _), ← img om h f (hex h hh f), ← img om h f' (hex h hh f'),
      tens_add, map_add]
  · apply eq_of_tens
    rw [tens_smul, ← img om h (c • f) (hex h hh _), ← img om h f (hex h hh f), tens_smul, map_smul]
  · apply archOp_eq_of_acts
    intro r _
    have e1 : om (1, 1) = 1 := map_one om
    rw [e1]
    rfl
  · have hmul : h * h' ∈ UAt σ W (evI F) := by
      intro u hu
      have e : mat (h * h') - 1 = (mat h - 1) * mat h' + (mat h' - 1) := by
        change mat h * mat h' - 1 = _
        noncomm_ring
      have a1 : u • (mat h - 1) = 0 := (show ∀ u, evI F u = 0 → u • (mat h - 1) = 0 from hh) u hu
      have a2 : u • (mat h' - 1) = 0 := (show ∀ u, evI F u = 0 → u • (mat h' - 1) = 0 from hh') u hu
      rw [e, smul_add, ← Matrix.smul_mul, a1, a2, zero_mul, add_zero]
    apply eq_of_tens
    rw [← img om (h * h') f (hex _ hmul f), ← img om h (archOp om h' f) (hex h hh _),
      ← img om h' f (hex h' hh' f)]
    have e2 : ((1 : UA σ X.J), h * h') = (1, h) * (1, h') := by rw [Prod.mk_mul_mk, one_mul]
    rw [e2, map_mul]
    rfl

end GlobalTheory.ArchLine
