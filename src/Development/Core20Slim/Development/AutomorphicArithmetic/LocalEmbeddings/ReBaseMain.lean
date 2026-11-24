module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRealmapsIsomorphism
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedFiniteMapsRestriction
public import Development.Core20Slim.Development.AutomorphicArithmetic.LocalEmbeddings.ReBaseReal
public import Development.Core20Slim.Development.AutomorphicArithmetic.LocalEmbeddings.ReBaseArch
public import Development.Core20Slim.Development.AutomorphicArithmetic.LocalEmbeddings.ReBaseZeta
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedDataRestrictionUnique
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedLocalIsomorphismScalars
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitPlaceCharacterComponentSmoothUnitaryConductStatement
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
public import Development.AbelianVarietyTheory.Definitions.Foundations.NonemptyAlgHomOfNotIsField
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchActionReadingsCompatible
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Classical
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.GroupWithZero.Action
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.IsApply
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Pi
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.UnitBall
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
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sets
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Multilinear.Basic
public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.ReBase

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {B : Base F E} {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E} {V : Spc F E a} {V' : Spc F E a'} {Z : Spc F E (a + a')}

theorem polMatch_iso {R R₃ : RealMaps F a a'} {Rf Rf₃ : FinMaps F a a'} {ψ₀ : R.Pi ≃ₗ[ℂ] R₃.Pi} {l₀ : ℂ}
    {ψ : ∀ v, Rf.Pi v ≃ₗ[ℂ] Rf₃.Pi v} {l : Pl (F := F) → ℂ} (hl1 : ∀ v ∉ X.T, l v = 1)
    (hR : ∀ f ∈ G.M.Pol B.ψ B.emb, R₃.p f = ψ₀ (R.p f)) (hR' : ∀ f ∈ G.M'.Pol B.ψ B.emb, R₃.p' f = l₀ • ψ₀ (R.p' f))
    (hRf : ∀ v, ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), Rf₃.p v φ = ψ v (Rf.p v φ))
    (hRf' : ∀ v, ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), Rf₃.p' v φ = l v • ψ v (Rf.p' v φ))
    {Φ Φ'} (hM : PolMatch B G X R Rf Φ Φ') : PolMatch B G X R₃ Rf₃ ((l₀ * ∏ v ∈ X.T, l v) • Φ) Φ' := by
  set Λ : ℂ := l₀ * ∏ v ∈ X.T, l v with hΛdef
  obtain ⟨T, hT, m, m', f, φ, f', φ', hf, hf', hΦ, hΦ', heq⟩ := hM
  have hΛT : l₀ * ∏ v ∈ T, l v = Λ := by
    rw [hΛdef, Finset.prod_subset hT (fun v _ hv => hl1 v hv)]
  refine ⟨T, hT, m, m', fun i => Λ • f i, φ, f', φ', fun i => ⟨Submodule.smul_mem _ _ (hf i).1, (hf i).2⟩, hf', ?_, hΦ', ?_⟩
  · rw [hΦ, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    funext x
    simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, mul_assoc]
  · let L := TensorProduct.map ψ₀.toLinearMap (PiTensorProduct.map fun v : T => (ψ v).toLinearMap)
    have h1 := congrArg L heq
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, L, TensorProduct.map_tmul, PiTensorProduct.map_tprod, LinearEquiv.coe_coe] at h1
    have lhs : ∀ i, R₃.p (Λ • f i) ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ fun v : T => Rf₃.p v (φ i v)) =
        Λ • (ψ₀ (R.p (f i)) ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ fun v : T => ψ v (Rf.p v (φ i v))) := by
      intro i
      have e : (fun v : T => Rf₃.p v (φ i v)) = fun v : T => ψ v (Rf.p v (φ i v)) :=
        funext fun v => hRf v _ ((hf i).2.1 v)
      rw [e, map_smul, hR _ (hf i).1, ← TensorProduct.smul_tmul']
    have rhs : ∀ j, R₃.p' (f' j) ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ fun v : T => Rf₃.p' v (φ' j v)) =
        Λ • (ψ₀ (R.p' (f' j)) ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ fun v : T => ψ v (Rf.p' v (φ' j v))) := by
      intro j
      have e : (fun v : T => Rf₃.p' v (φ' j v)) = fun v : T => l v • ψ v (Rf.p' v (φ' j v)) :=
        funext fun v => hRf' v _ ((hf' j).2.1 v)
      rw [e, MultilinearMap.map_smul_univ, hR' _ (hf' j).1, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_smul]
      simp only [RingHom.id_apply]
      rw [Finset.prod_coe_sort, hΛT]
    simp only [lhs, rhs, ← Finset.smul_sum, h1]


variable (B G V V' Z) in
def kapId : (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))ˣ :=
  ∏ v : B.P, locIdele F (splitPrime (B.τ v))
    (Units.map (complMap (splitPrime_under (B.τ v))).toMonoidHom (kap G V V' Z v.1))

theorem chr_kapId (χ : Chr F E) :
    (χ (kapId B G V V' Z) : ℂ) = ∏ v : B.P, (chrW χ (B.τ v) (kap G V V' Z v.1) : ℂ) := by
  rw [kapId, map_prod]
  exact map_prod Circle.coeHom _ _

variable {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}


theorem acts_pureA {κ : Type} [Fintype κ] {T : ((κ → AF F) → ℂ) → (κ → AF F) → ℂ} {f f₁ : SInf F κ}
    (h : Acts (evI F) T f f₁) {g : (κ → Af F) → ℂ} (hg : g ∈ SB (κ → Af F)) : T (pureA F f g) = pureA F f₁ g := by
  refine h (fun x => g fun i => (x i).2) ⟨fun x z hz => ?_, Submodule.subset_span ⟨f, g, hg, rfl⟩⟩
  show g (fun i => (x i + z i).2) = g (fun i => (x i).2)
  congr 1
  funext i
  show (x i).2 + (z i).2 = (x i).2
  rw [GlobalTheory.RealLift.fin_eq_zero_of_at hz i, add_zero]

theorem pureA_smul {κ : Type} [Fintype κ] (c : ℂ) (f : SInf F κ) (g : (κ → Af F) → ℂ) :
    pureA F (⇑(c • f)) g = c • pureA F f g := by
  funext x
  simp only [pureA, SchwartzMap.smul_apply, smul_eq_mul, Pi.smul_apply, mul_assoc]

theorem acts_congr {κ : Type} [Fintype κ] {T T₁ : ((κ → AF F) → ℂ) → (κ → AF F) → ℂ} (e : ∀ Φ ∈ schA F κ, T Φ = T₁ Φ)
    {f f₁ : (κ → mixedEmbedding.mixedSpace F) → ℂ} (h : Acts (evI F) T f f₁) : Acts (evI F) T₁ f f₁ :=
  fun r hr => (e _ hr.2).symm.trans (h r hr)

end GlobalTheory.ReBase

end
