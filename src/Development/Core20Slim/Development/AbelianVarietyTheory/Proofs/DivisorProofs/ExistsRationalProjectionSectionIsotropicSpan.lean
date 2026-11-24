module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReindexDblIncM
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.LagrInt
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Classical
public import Init.Core
public import Init.Data.Zero
public import Init.Ext
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Action.Prod
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Prod
public import Mathlib.Algebra.Module.Projective
public import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Ker
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Module.Submodule.LinearMap
public import Mathlib.Algebra.Module.Submodule.Map
public import Mathlib.Algebra.Module.Submodule.Range
public import Mathlib.Algebra.Module.Submodule.RestrictScalars
public import Mathlib.Algebra.Module.Torsion.Pi
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.CompleteLattice.Defs
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Disjoint
public import Mathlib.RingTheory.Bialgebra.Basic
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Finiteness.Prod
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TotallySplit

@[expose] public section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

namespace GlobalTheory

theorem rational_proj_section_of_span : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
    (S : Submodule (AF F) ((κ → AF F) × (κ → AF F))),
    S ≤ Submodule.span (AF F) {s | s ∈ S ∧ ∃ y z : κ → F,
      s = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))} →
    ∃ P Q : Matrix κ κ F,
      (∀ s ∈ S, (P.map (algebraMap F (AF F))) *ᵥ s.1 = 0) ∧
      (∀ s ∈ S, (s.1, (Q.map (algebraMap F (AF F))) *ᵥ s.1) ∈ S) ∧
      (∀ ξ : κ → F, P *ᵥ ξ = 0 →
        ((fun i => algebraMap F (AF F) (ξ i)), (fun i => algebraMap F (AF F) ((Q *ᵥ ξ) i))) ∈ S) := by
  intro F _ _ κ _ S hS
  classical
  let ι := algebraMap F (AF F)
  let Φ : ((κ → F) × (κ → F)) →ₗ[F] ((κ → AF F) × (κ → AF F)) :=
    LinearMap.prodMap ((Algebra.linearMap F (AF F)).compLeft κ) ((Algebra.linearMap F (AF F)).compLeft κ)
  let T : Submodule F ((κ → F) × (κ → F)) := (S.restrictScalars F).comap Φ
  have hT : ∀ y z, (y, z) ∈ T ↔ ((fun i => ι (y i)), (fun i => ι (z i))) ∈ S := fun y z => Iff.rfl
  let f : T →ₗ[F] (κ → F) := LinearMap.fst F _ _ ∘ₗ T.subtype
  let L₁ := LinearMap.range f
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl L₁
  obtain ⟨g, hg⟩ := LinearMap.exists_rightInverse_of_surjective f.rangeRestrict (LinearMap.range_rangeRestrict f)
  let π : (κ → F) →ₗ[F] (κ → F) := C.subtype ∘ₗ Submodule.linearProjOfIsCompl C L₁ hC.symm
  let q : (κ → F) →ₗ[F] (κ → F) := LinearMap.snd F _ _ ∘ₗ T.subtype ∘ₗ g ∘ₗ Submodule.linearProjOfIsCompl L₁ C hC
  have hπ : ∀ y, π y = 0 ↔ y ∈ L₁ := by
    intro y
    simp only [π, LinearMap.comp_apply, Submodule.coe_subtype, ZeroMemClass.coe_eq_zero]
    exact Submodule.linearProjOfIsCompl_apply_eq_zero_iff hC.symm
  have hq : ∀ y ∈ L₁, (y, q y) ∈ T := by
    intro y hy
    have h1 : Submodule.linearProjOfIsCompl L₁ C hC y = ⟨y, hy⟩ :=
      Submodule.linearProjOfIsCompl_apply_left hC ⟨y, hy⟩
    have h2 : f.rangeRestrict (g ⟨y, hy⟩) = ⟨y, hy⟩ := LinearMap.congr_fun hg ⟨y, hy⟩
    have h3 : ((g ⟨y, hy⟩ : T) : (κ → F) × (κ → F)).1 = y := by
      have := congrArg Subtype.val h2
      simpa [f] using this
    have hm := (g ⟨y, hy⟩).2
    have e : ((g ⟨y, hy⟩ : T) : (κ → F) × (κ → F)) = (y, q y) := by
      ext1
      · exact h3
      · simp [q, h1]
    rw [← e]; exact hm
  have hL : ∀ y z, (y, z) ∈ T → y ∈ L₁ := fun y z h => ⟨⟨(y, z), h⟩, rfl⟩
  have hmv : ∀ (M : Matrix κ κ F) (v : κ → F),
      (M.map ι) *ᵥ (fun i => ι (v i)) = fun i => ι ((M *ᵥ v) i) := by
    intro M v; funext i
    exact (RingHom.map_mulVec ι M v i).symm
  refine ⟨LinearMap.toMatrix' π, LinearMap.toMatrix' q, ?_, ?_, ?_⟩
  · intro s hs
    let A : ((κ → AF F) × (κ → AF F)) →ₗ[AF F] (κ → AF F) :=
      (Matrix.mulVecLin ((LinearMap.toMatrix' π).map ι)) ∘ₗ LinearMap.fst _ _ _
    have hle : Submodule.span (AF F) {s | s ∈ S ∧ ∃ y z : κ → F,
        s = (fun i => ι (y i), fun i => ι (z i))} ≤ LinearMap.ker A := by
      rw [Submodule.span_le]
      rintro _ ⟨hs', y, z, rfl⟩
      have hy : y ∈ L₁ := hL y z hs'
      have h0 : π y = 0 := (hπ y).2 hy
      show (LinearMap.toMatrix' π).map ι *ᵥ (fun i => ι (y i)) = 0
      rw [hmv, LinearMap.toMatrix'_mulVec, h0]
      funext i; simp
    exact hle (hS hs)
  · intro s hs
    let B : ((κ → AF F) × (κ → AF F)) →ₗ[AF F] ((κ → AF F) × (κ → AF F)) :=
      LinearMap.prod (LinearMap.fst _ _ _)
        ((Matrix.mulVecLin ((LinearMap.toMatrix' q).map ι)) ∘ₗ LinearMap.fst _ _ _)
    have hle : Submodule.span (AF F) {s | s ∈ S ∧ ∃ y z : κ → F,
        s = (fun i => ι (y i), fun i => ι (z i))} ≤ S.comap B := by
      rw [Submodule.span_le]
      rintro _ ⟨hs', y, z, rfl⟩
      have hy : y ∈ L₁ := hL y z hs'
      show ((fun i => ι (y i)), (LinearMap.toMatrix' q).map ι *ᵥ (fun i => ι (y i))) ∈ S
      rw [hmv, LinearMap.toMatrix'_mulVec]
      exact hq y hy
    exact hle (hS hs)
  · intro ξ hξ
    rw [LinearMap.toMatrix'_mulVec] at hξ
    have hx : ξ ∈ L₁ := (hπ ξ).1 hξ
    rw [LinearMap.toMatrix'_mulVec]
    exact hq ξ hx

end GlobalTheory
