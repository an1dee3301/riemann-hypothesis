module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.AlgAtLeAlgD
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Classical
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
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
public import Mathlib.Algebra.Module.Submodule.LinearMap
public import Mathlib.Algebra.Module.Submodule.Map
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
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

namespace GlobalTheory.HoweGlobal

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}

def opInf (Bs : Base F E) (G : Geo σ a a') (om : Rep σ G.V G.W) : Set (Module.End ℂ ↥(G.M.Pol Bs.ψ Bs.emb)) :=
  {g | (∃ k ∈ KInf σ G.W Bs.emb, ∀ f : ↥(G.M.Pol Bs.ψ Bs.emb),
      Acts (evI F) (om (1, k)) ⇑(f : SInf F (Fin a × Fin (a + a'))) ⇑((g f : ↥(G.M.Pol Bs.ψ Bs.emb)) : SInf F _)) ∨
    ∃ γ ∈ Lines σ G.W, ∀ f : ↥(G.M.Pol Bs.ψ Bs.emb),
      ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) ⇑(f : SInf F (Fin a × Fin (a + a')))
        ⇑((g f : ↥(G.M.Pol Bs.ψ Bs.emb)) : SInf F _)}

def relInf (Bs : Base F E) (G : Geo σ a a') (om : Rep σ G.V G.W) : Submodule ℂ ↥(G.M.Pol Bs.ψ Bs.emb) :=
  Submodule.span ℂ {x | (∃ γ ∈ Lines σ G.V, ∃ f ∈ G.M.Pol Bs.ψ Bs.emb,
      ActsD (evI F) (fun t => om (γ (Multiplicative.ofAdd t), 1)) ⇑f ⇑(x : SInf F (Fin a × Fin (a + a')))) ∨
    ∃ k ∈ KInf σ G.V Bs.emb, ∃ f f₁ : ↥(G.M.Pol Bs.ψ Bs.emb),
      Acts (evI F) (om (k, 1)) ⇑(f : SInf F (Fin a × Fin (a + a'))) ⇑(f₁ : SInf F (Fin a × Fin (a + a'))) ∧ x = f₁ - f}

def opFin (G : Geo σ a a') (om : Rep σ G.V G.W) (v : Pl F) :
    Set (Module.End ℂ ↥(SB (Fin a × Fin (a + a') → Fv F v))) :=
  {g | ∃ h ∈ UAt σ G.W (evFin F v), ∀ φ : ↥(SB (Fin a × Fin (a + a') → Fv F v)),
    Acts (evFin F v) (om (1, h)) (φ : (Fin a × Fin (a + a') → Fv F v) → ℂ)
      ((g φ : ↥(SB (Fin a × Fin (a + a') → Fv F v))) : (Fin a × Fin (a + a') → Fv F v) → ℂ)}

def relFin (G : Geo σ a a') (om : Rep σ G.V G.W) (v : Pl F) : Submodule ℂ ↥(SB (Fin a × Fin (a + a') → Fv F v)) :=
  (augAt om v).comap (SB (Fin a × Fin (a + a') → Fv F v)).subtype

end GlobalTheory.HoweGlobal

end
