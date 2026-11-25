module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealMapsTwoTriplesAgree
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilOperatorsEqAtRealPlacesSameExponentsStatement
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Classical
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
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
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sets
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.RealMapsChars
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
variable {F : Type} [Field F] [NumberField F]
end GlobalTheory.RealMapsChars
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealMapsChars in
theorem GlobalTheory.RealMapsChars.real_embeddings_of_characters_of_same_exponent : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xa Xb : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) oa oa' ob ob' R,
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B Γ Xa oa oa' → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B Γ Xb ob ob' →
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsRealMaps B Γ oa oa' R → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsRealMaps B Γ ob ob' R := by
  intro hP F E _ _ _ _ _ σ B a a' Γ Xa Xb oa oa' ob ob' R hA hB hR
  obtain ⟨hV, hV'⟩ := GlobalTheory.T.weilOperators_eq_at_realPlaces_same_exponents F E σ B a a' Γ Xa Xb oa oa' ob ob' hA hB
  have lV : ∀ g ∈ UAt σ Γ.V (evI F), ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin a × Fin (a + a')), oa (g, 1) Φ = ob (g, 1) Φ :=
    fun g hg Φ hΦ => hV g 1 hg one_mem_uAt Φ hΦ
  have lV' : ∀ g ∈ UAt σ Γ.V' (evI F), ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin a' × Fin (a + a')), oa' (g, 1) Φ = ob' (g, 1) Φ :=
    fun g hg Φ hΦ => hV' g 1 hg one_mem_uAt Φ hΦ
  have lW : ∀ h ∈ UAt σ Γ.W (evI F), ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin a × Fin (a + a')), oa (1, h) Φ = ob (1, h) Φ :=
    fun h hh Φ hΦ => hV 1 h one_mem_uAt hh Φ hΦ
  have lW' : ∀ h ∈ UAt σ Γ.W (evI F), ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin a' × Fin (a + a')), oa' (1, h) Φ = ob' (1, h) Φ :=
    fun h hh Φ hΦ => hV' 1 h one_mem_uAt hh Φ hΦ
  have bV : ∀ g ∈ UAt σ Γ.V (evI F), ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin a × Fin (a + a')), ob (g, 1) Φ = oa (g, 1) Φ :=
    fun g hg Φ hΦ => (lV g hg Φ hΦ).symm
  have bV' : ∀ g ∈ UAt σ Γ.V' (evI F), ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin a' × Fin (a + a')), ob' (g, 1) Φ = oa' (g, 1) Φ :=
    fun g hg Φ hΦ => (lV' g hg Φ hΦ).symm
  have bW : ∀ h ∈ UAt σ Γ.W (evI F), ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin a × Fin (a + a')), ob (1, h) Φ = oa (1, h) Φ :=
    fun h hh Φ hΦ => (lW h hh Φ hΦ).symm
  have bW' : ∀ h ∈ UAt σ Γ.W (evI F), ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin a' × Fin (a + a')), ob' (1, h) Φ = oa' (1, h) Φ :=
    fun h hh Φ hΦ => (lW' h hh Φ hΦ).symm
  refine ⟨⟨hR.quot.onto, ?_, ?_⟩, ⟨hR.quot'.onto, ?_, ?_⟩, ?_, ?_, hR.nontriv, ?_⟩
  · intro γ hγ f hf f₁ h
    exact hR.quot.lie γ hγ f hf f₁ (actsD_of_eqOn (fun t => bV _ (hγ.2 _)) h)
  · intro k hk f hf f₁ h
    exact hR.quot.cpt k hk f hf f₁ (acts_of_eqOn (bV k hk.1) h)
  · intro γ hγ f hf f₁ h
    exact hR.quot'.lie γ hγ f hf f₁ (actsD_of_eqOn (fun t => bV' _ (hγ.2 _)) h)
  · intro k hk f hf f₁ h
    exact hR.quot'.cpt k hk f hf f₁ (acts_of_eqOn (bV' k hk.1) h)
  · intro γ hγ f hf f' hf' f₁ f₁' h h'
    exact hR.lie γ hγ f hf f' hf' f₁ f₁' (actsD_of_eqOn (fun t => bW _ (hγ.2 _)) h)
      (actsD_of_eqOn (fun t => bW' _ (hγ.2 _)) h')
  · intro k hk f hf f' hf' f₁ f₁' h h'
    exact hR.cpt k hk f hf f' hf' f₁ f₁' (acts_of_eqOn (bW k hk.1) h) (acts_of_eqOn (bW' k hk.1) h')
  · intro N h1 h2
    refine hR.irred N (fun γ hγ f hf f₁ h => h1 γ hγ f hf f₁ (actsD_of_eqOn (fun t => lW _ (hγ.2 _)) h))
      (fun k hk f hf f₁ h => h2 k hk f hf f₁ (acts_of_eqOn (lW k hk.1) h))
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.characters_real_valued_of_equal_exponent : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xa Xb : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) oa oa' ob ob' R,
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B Γ Xa oa oa' → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B Γ Xb ob ob' →
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsRealMaps B Γ oa oa' R → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsRealMaps B Γ ob ob' R := by
  first | exact @_root_.GlobalTheory.RealMapsChars.real_embeddings_of_characters_of_same_exponent | exact _root_.GlobalTheory.RealMapsChars.real_embeddings_of_characters_of_same_exponent | (intros; apply _root_.GlobalTheory.RealMapsChars.real_embeddings_of_characters_of_same_exponent <;> assumption)
end
