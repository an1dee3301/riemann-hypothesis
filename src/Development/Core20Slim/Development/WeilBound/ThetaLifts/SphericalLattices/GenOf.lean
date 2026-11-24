module

public import Development.Core20Slim.Development.WeilBound.ThetaLifts.SphericalLattices.HoweDefs
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.SatakeParameters.RhoMemOfMkEq
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.Core20Slim.Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.InertDef
public import Formalism.SatakeDualWeyl.Statement
public import Formalism.SatakeDualWeyl.StatementF
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
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
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Module.Submodule.LinearMap
public import Mathlib.Algebra.Module.Submodule.Map
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.Algebra.Valued.ValuationTopology
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.UniformSpace.Cauchy
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

namespace PositivityTheory.Sph

open scoped Matrix
open NumberField IsDedekindDomain Topology GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PositivityTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}

theorem gen_of {X : Spc F E n} {W : Spc F E d} {M : Model σ X W} {ψ : AddChar (AF F) ℂ} {om : Rep σ X W} {v : Pl F}
    {ω : UA σ X.J × UA σ W.J → Module.End ℂ (Fn F n d v)} {ρ : Matrix (Fin n) (Fin d) (AE F E) → Module.End ℂ (Fn F n d v)}
    (hL : IsLocRep M ψ om v ω ρ) (hD : LocData M om v) :
    (∀ φ ∈ SB _, (∀ g ∈ KAt σ X v, ω (g, 1) φ = φ) →
      φ ∈ Submodule.span ℂ {z | ∃ h ∈ UAt σ W (evFin F v), z = ω (1, h) (M.vac v)}) ∧
    (∀ φ ∈ SB _, (∀ k ∈ KAt σ W v, ω (1, k) φ = φ) →
      φ ∈ Submodule.span ℂ {z | ∃ g ∈ UAt σ X (evFin F v), z = ω (g, 1) (M.vac v)}) := by
  obtain ⟨L, _, _, _, _, ϖ, σL, q, δ, JS, JT, ψL, ρL, ωL, ιS, ιT, s, hP, hs0, hsv, hspan, hsvac,
    hιS, hιT, hKS, hKT, hLoc⟩ := hD
  obtain ⟨h1, h2⟩ := GlobalTheory.Hk3.howeUnram_holds _ _ _ _ _ _ _ _ _ _ _ _ _ hP s hs0 hsv hspan
  have key : ∀ g h m, (↑(ωL (g, h) m) : Fn F n d v) = ω (ιS g, ιT h) ↑m := by
    intro g h m
    have hφ₁ := hL.pres _ (hιS g) _ (hιT h) _ m.2
    exact (hLoc g h m _ hφ₁).1 ((hL.acts _ (hιS g) _ (hιT h) _ m.2 _).2 rfl)
  have hS1 : ιS 1 = 1 := map_one ιS
  have hT1 : ιT 1 = 1 := map_one ιT
  constructor
  · intro φ hφ hfix
    have hw := h1 ⟨φ, hφ⟩ fun g hg => by
      apply Subtype.ext
      rw [key, hT1]
      exact hfix _ (by rw [kAt_eq]; exact hKS g hg)
    have hmap := Submodule.mem_map_of_mem (f := Submodule.subtype _) hw
    rw [Submodule.map_span] at hmap
    refine Submodule.span_mono ?_ hmap
    rintro _ ⟨_, ⟨h, rfl⟩, rfl⟩
    simp only [Set.mem_ofPred_eq]
    exact ⟨ιT h, hιT h, by rw [Submodule.subtype_apply, key, hS1, hsvac]⟩
  · intro φ hφ hfix
    have hw := h2 ⟨φ, hφ⟩ fun h hh => by
      apply Subtype.ext
      rw [key, hS1]
      exact hfix _ (by rw [kAt_eq]; exact hKT h hh)
    have hmap := Submodule.mem_map_of_mem (f := Submodule.subtype _) hw
    rw [Submodule.map_span] at hmap
    refine Submodule.span_mono ?_ hmap
    rintro _ ⟨_, ⟨g, rfl⟩, rfl⟩
    simp only [Set.mem_ofPred_eq]
    exact ⟨ιS g, hιS g, by rw [Submodule.subtype_apply, key, hT1, hsvac]⟩

end PositivityTheory.Sph

end
