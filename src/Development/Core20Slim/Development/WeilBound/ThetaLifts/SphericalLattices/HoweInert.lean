module

public import Development.Core20Slim.Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HoweMaximalTori.MaxSplit
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityUnitary
public import Development.Core20Slim.Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.InertDef
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Invertible.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Indicator
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.Kleene
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Pi
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.IsEmpty.Basic
public import Mathlib.Basic.IsEmpty.Defs
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Defs.Lattice
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Valuation.Integers
public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

namespace PositivityTheory.Sph

open scoped Matrix
open NumberField IsDedekindDomain Topology ValuativeRel GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PositivityTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
  {X : Spc F E n} {W : Spc F E d}

structure IsSph (om : Rep σ X W) (v : Pl F) (ω : UA σ X.J × UA σ W.J → Module.End ℂ (Fn F n d v)) (s : Fn F n d v) : Prop where
  mem : s ∈ SB _
  gen : ∀ φ ∈ SB _, φ ∈ augAt om v ⊔ Submodule.span ℂ {z | ∃ h ∈ UAt σ W (evFin F v), z = ω (1, h) s}
  line : ∀ φ ∈ SB _, ∃ (m : ℕ) (k : Fin (m + 1) → UA σ W.J) (w : Fin (m + 1) → ℂ) (c : ℂ),
    (∀ i, k i ∈ UAt σ W (evFin F v) ∧ w i • ω (1, k i) s = s) ∧ ∑ i, w i • ω (1, k i) φ - c • s ∈ augAt om v

def SphAt (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (om : Rep σ X W) (v : Pl F) : Prop :=
  ∀ ω ρ, IsLocRep M ψ om v ω ρ → ∃ s, IsSph om v ω s

def IrrAt (om : Rep σ X W) (v : Pl F) : Prop := ∀ N, GlobalTheory.Published.ThetaSub om v N → N = augAt om v ∨ N = SB _

structure IsHowe (M : Model σ X W) (v : Pl F) (ω : UA σ X.J × UA σ W.J → Module.End ℂ (Fn F n d v)) : Prop where
  fixX : ∀ g ∈ KAt σ X v, ω (g, 1) (M.vac v) = M.vac v
  fixW : ∀ k ∈ KAt σ W v, ω (1, k) (M.vac v) = M.vac v
  genW : ∀ φ ∈ SB _, (∀ g ∈ KAt σ X v, ω (g, 1) φ = φ) →
    φ ∈ Submodule.span ℂ {z | ∃ h ∈ UAt σ W (evFin F v), z = ω (1, h) (M.vac v)}
  genX : ∀ φ ∈ SB _, (∀ k ∈ KAt σ W v, ω (1, k) φ = φ) →
    φ ∈ Submodule.span ℂ {z | ∃ g ∈ UAt σ X (evFin F v), z = ω (g, 1) (M.vac v)}

structure IsVacSph (M : Model σ X W) (om : Rep σ X W) (v : Pl F) (ω : UA σ X.J × UA σ W.J → Module.End ℂ (Fn F n d v)) : Prop where
  fixW : ∀ k ∈ KAt σ W v, ω (1, k) (M.vac v) = M.vac v
  gen : ∀ φ ∈ SB _, φ ∈ augAt om v ⊔ Submodule.span ℂ {z | ∃ h ∈ UAt σ W (evFin F v), z = ω (1, h) (M.vac v)}
  line : ∀ φ ∈ SB _, ∃ (m : ℕ) (k : Fin (m + 1) → UA σ W.J) (c : ℂ),
    (∀ i, k i ∈ KAt σ W v) ∧ ∑ i, ω (1, k i) φ - c • M.vac v ∈ augAt om v


def AllTri (Q : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}
    (_ : Base F E) (G : Geo σ a a') (_ : Rep σ G.V G.W) (_ : Rep σ G.V' G.W), Pl F → Prop) : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ)
    (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → ∀ v, Q B G om om' v

def LatSt : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n d : ℕ),
    ∀ Φ ∈ SB (Matrix (Fin n) (Fin d) k), (∀ g ∈ GlobalTheory.SplitWeil.KO k (Fin n), ∀ Y, Φ ((g : GL (Fin n) k).1 * Y) = Φ Y) →
      Φ ∈ Submodule.span ℂ {f | ∃ h : GL (Fin d) k,
        f = fun Y => Set.indicator {Z : Matrix (Fin n) (Fin d) k | ∀ i j, Z i j ∈ 𝒪[k]} (fun _ => (1 : ℂ)) (Y * h.1)}

def SphSplit : Prop := AllTri fun {F E} _ _ _ _ _ {_ _ _} B G om om' v => Nonempty (E →ₐ[F] Fv F v) →
  (SphAt G.M B.ψ om v ∨ IrrAt om v) ∧ (SphAt G.M' B.ψ om' v ∨ IrrAt om' v)

def HoweInert : Prop := AllTri fun {F E} _ _ _ _ _ {_ _ _} B G om om' v => IsEmpty (E →ₐ[F] Fv F v) →
  (∀ ω ρ, IsLocRep G.M B.ψ om v ω ρ → IsHowe G.M v ω) ∧ ∀ ω ρ, IsLocRep G.M' B.ψ om' v ω ρ → IsHowe G.M' v ω

def VacInert : Prop := AllTri fun {F E} _ _ _ _ _ {_ _ _} B G om om' v => IsEmpty (E →ₐ[F] Fv F v) →
  (∀ ω ρ, IsLocRep G.M B.ψ om v ω ρ → IsVacSph G.M om v ω) ∧ ∀ ω ρ, IsLocRep G.M' B.ψ om' v ω ρ → IsVacSph G.M' om' v ω


def SphTri : Prop := AllTri fun B G om om' v =>
  (SphAt G.M B.ψ om v ∨ IrrAt om v) ∧ (SphAt G.M' B.ψ om' v ∨ IrrAt om' v)

theorem IsVacSph.isSph {M : Model σ X W} {om : Rep σ X W} {v : Pl F} {ω} (h : IsVacSph M om v ω) (hs : M.vac v ∈ SB _) :
    IsSph om v ω (M.vac v) :=
  ⟨hs, h.gen, fun φ hφ => by
    obtain ⟨m, k, c, h1, h2⟩ := h.line φ hφ
    exact ⟨m, k, fun _ => 1, c, fun i => ⟨(h1 i).1, by rw [one_smul, h.fixW _ (h1 i)]⟩, by simpa using h2⟩⟩

theorem sphTri_of (h1 : SphSplit) (h2 : VacInert) : SphTri := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v
  rcases isEmpty_or_nonempty (E →ₐ[F] Fv F v) with he | he
  · obtain ⟨p, q⟩ := h2 F E σ B a a' G X om om' hT v he
    exact ⟨Or.inl fun ω ρ L => ⟨_, (p ω ρ L).isSph (hT.geo.hM.vac v).1⟩,
      Or.inl fun ω ρ L => ⟨_, (q ω ρ L).isSph (hT.geo.hM'.vac v).1⟩⟩
  · exact h1 F E σ B a a' G X om om' hT v he

end PositivityTheory.Sph

end
