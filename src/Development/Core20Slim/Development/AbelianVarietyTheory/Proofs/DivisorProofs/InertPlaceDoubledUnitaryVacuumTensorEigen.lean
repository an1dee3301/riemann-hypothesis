module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.FromBlocksMem
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductFunctionOnSumCoordsMemAdelicSchwartzSpace
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.StarMemAdelicSchwartzSpaceNumberField
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearFormEqZeroOfKillsProductSchwartzBruhat
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledWeilRepresentationLocalityFinitePlaceStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledVacuumTwistedVacuumConditionDoubledLatticStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledVacuumConditionStableLatticeStabilizerIneStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceDoubledVacuumConditionUniqueStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
public import Formalism.SatakeDualWeyl.StatementG
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Invertible.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.WithOne.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Support
public import Mathlib.Topology.Algebra.Valued.NormedValued
public import Mathlib.Topology.Connected.Separation
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.InertDblLine

theorem line : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w →
    ∀ (dd : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J))) (Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a')))
      (omd : UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J)) →* Module.End ℂ ((Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a') → AF F) → ℂ)),
      IsDblCoord (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) G.M'.co dd →
      IsUWeilSplit (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (adeleClass F) B.ψ (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J)) dd X.α (diagCols (Fin (a + a'))) omd →
    ∀ R : (Fin a' × Fin (a + a') → AF F) → ℂ, Rest (evFin F v) (G.M'.vac v) R →
    ∀ g ∈ GlobalTheory.InertDbl.KAtD σ G.W v, ∃ c : ℂ, omd g (GlobalTheory.InertDbl.dblFun (tens (evFin F v) (G.M'.vac v) R)) =
      c • GlobalTheory.InertDbl.dblFun (tens (evFin F v) (G.M'.vac v) R) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hTr v w hw dd omd hdd hsp R hR g hg
  obtain ⟨hvSB, hv0, θ, hθ, hvac⟩ := hTr.geo.hM'.vac v
  set φ₀ := boxFun (G.M'.vac v) (fun x => star (G.M'.vac v x)) with hφ₀
  set r₀ : ((Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a')) → AF F) → ℂ := boxFun R (fun x => star (R x)) with hr₀
  have hΦ : GlobalTheory.InertDbl.dblFun (tens (evFin F v) (G.M'.vac v) R) = tens (evFin F v) φ₀ r₀ := by
    funext x
    show (_ * _) * star (_ * _) = (_ * _) * (_ * _)
    rw [star_mul']
    exact mul_mul_mul_comm _ _ _ _
  have hstar : (fun x => star (G.M'.vac v x)) ∈ SB (Fin a' × Fin (a + a') → Fv F v) :=
    ⟨hvSB.1.comp star, hvSB.2.comp_left (g := star) (star_zero ℂ)⟩
  have hφ₀SB : φ₀ ∈ SB _ := GlobalTheory.BoxSpan.boxFun_mem_SB' hvSB hstar
  have hRest : Rest (evFin F v) φ₀ r₀ := by
    refine ⟨fun x z hz => ?_, ?_⟩
    · have hl : At (evFin F v) (z ∘ Sum.inl) := fun u hu => by
        funext i; exact congrFun (hz u hu) (Sum.inl i)
      have hr : At (evFin F v) (z ∘ Sum.inr) := fun u hu => by
        funext i; exact congrFun (hz u hu) (Sum.inr i)
      simp only [hr₀, boxFun]
      rw [show (x + z) ∘ Sum.inl = x ∘ Sum.inl + z ∘ Sum.inl from rfl,
        show (x + z) ∘ Sum.inr = x ∘ Sum.inr + z ∘ Sum.inr from rfl, hR.1 _ _ hl, hR.1 _ _ hr]
    · rw [← hΦ]
      exact GlobalTheory.SchwartzBox.boxFun_mem_schA F _ _ _ hR.2 _ (GlobalTheory.SchAConj.star_mem_schA F _ _ hR.2)
  obtain ⟨φ₁, hφ₁, hact⟩ := GlobalTheory.T.doubledWeilRepresentation_locality_finitePlace F E σ B a a' G X om om' hTr v dd omd hsp g hg.1 φ₀ hφ₀SB
  have h₀ := GlobalTheory.T.doubledVacuum_twistedVacuumCondition_doubledLattice F E σ B a a' G X om om' hTr v dd hdd θ hθ hvac
  have h₁ := GlobalTheory.T.doubledVacuumCondition_stable_latticeStabilizer_inert F E σ B a a' G X om om' hTr v dd omd hsp θ hθ g hg φ₀ hφ₀SB φ₁ hφ₁ h₀ hact
  obtain ⟨c, hc⟩ := GlobalTheory.T.inertPlace_doubledVacuumCondition_unique F E σ B a a' G X om om' hTr v w hw dd hdd θ hθ hvac φ₁ hφ₁ h₁
  refine ⟨c, ?_⟩
  rw [hΦ, hact r₀ hRest, hc]
  funext x
  simp only [tens, Pi.smul_apply, smul_eq_mul]
  ring

end GlobalTheory.InertDblLine
