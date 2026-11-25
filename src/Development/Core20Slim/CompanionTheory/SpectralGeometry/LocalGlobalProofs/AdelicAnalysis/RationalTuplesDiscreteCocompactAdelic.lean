module

public import Mathlib
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.HypJ
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelesLocallyCompactSecondCountable
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdeleRingCocompactDiscreteNumberFieldStatement
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import Init.Classical
public import Init.Core
public import Init.Data.Function
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Rat
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Finsupp.SMul
public import Mathlib.Data.Finsupp.SMulWithZero
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Image
public import Mathlib.Data.Set.Operations
public import Mathlib.FieldTheory.Perfect
public import Mathlib.FieldTheory.Separable
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Free
public import Mathlib.RingTheory.Trace.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Separation.Hausdorff

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.CocW

theorem repr_inclR {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    {d : ℕ} (b : Module.Basis (Fin d) F E) (e : E) (k : Fin d) :
    (Algebra.TensorProduct.basis R b).repr (inclR R e) k = algebraMap F R (b.repr e k) := by
  have : inclR (F := F) R e = (1 : R) ⊗ₜ[F] e := rfl
  rw [this, Algebra.TensorProduct.basis_repr_tmul]
  simp

theorem scalar (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (h : IsCMExt F E σ) :
    (∃ C : Set (AF F ⊗[F] E), IsCompact C ∧ ∀ y, ∃ e : E, y - inclR (AF F) e ∈ C) ∧
    (∀ C : Set (AF F ⊗[F] E), IsCompact C → {e : E | inclR (AF F) e ∈ C}.Finite) ∧
    NoncompactSpace (AF F ⊗[F] E) := by
  obtain ⟨⟨hlc, hsc, ht2⟩, -⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  obtain ⟨hC, hfin, hnc⟩ := GlobalTheory.T.adele_ring_cocompact_discrete_number_field F
  obtain ⟨-, -, -, -, -, -, hb, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ h (AF F)
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have hd : 0 < Module.finrank F E := by rw [h.2.2.1]; norm_num
  let b := Module.finBasis F E
  let φ : AF F ⊗[F] E → Fin (Module.finrank F E) → AF F :=
    fun y k => (Algebra.TensorProduct.basis (AF F) b).repr y k
  have hφ : IsHomeomorph φ := hb _ b
  have hcont : ∀ k, Continuous fun y => φ y k := fun k => (continuous_apply k).comp hφ.continuous
  have hsub : ∀ y e k, φ (y - inclR (AF F) e) k = φ y k - algebraMap F (AF F) (b.repr e k) := by
    intro y e k
    simp only [φ, map_sub, Finsupp.sub_apply, repr_inclR]
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨C, hCc, hCy⟩ := hC
    refine ⟨φ ⁻¹' Set.pi Set.univ fun _ => C, ?_, ?_⟩
    · exact (hφ.homeomorph φ).isCompact_preimage.2 (isCompact_univ_pi fun _ => hCc)
    · intro y
      choose l hl using fun k => hCy (φ y k)
      refine ⟨∑ k, l k • b k, ?_⟩
      intro k _
      rw [hsub, b.repr_sum_self]
      exact hl k
  · intro C hCc
    have hS : ∀ k, {l : F | algebraMap F (AF F) l ∈ (fun y => φ y k) '' C}.Finite :=
      fun k => hfin _ (hCc.image (hcont k))
    refine ((Set.Finite.pi hS).preimage (f := fun (e : E) k => b.repr e k) ?_).subset ?_
    · intro x _ y _ hxy
      apply b.repr.injective
      ext k
      exact congrFun hxy k
    · intro e he k _
      refine ⟨inclR (AF F) e, he, ?_⟩
      exact repr_inclR (AF F) b e k
  · refine ⟨fun hK => hnc.noncompact_univ ?_⟩
    have hsurj : Function.Surjective fun y => φ y ⟨0, hd⟩ := by
      intro r
      obtain ⟨y, hy⟩ := hφ.surjective fun _ => r
      exact ⟨y, congrFun hy _⟩
    have := hK.image (hcont ⟨0, hd⟩)
    rwa [Set.image_univ, hsurj.range_eq] at this

theorem main : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n M : ℕ), (∃ C : Set (Fin n → Fin M → AF F ⊗[F] E), IsCompact C ∧ ∀ y, ∃ X : Fin n → Fin M → E, y - ratTup (AF F) X ∈ C) ∧ (∀ C : Set (Fin n → Fin M → AF F ⊗[F] E), IsCompact C → {X : Fin n → Fin M → E | ratTup (AF F) X ∈ C}.Finite) ∧ (0 < n → 0 < M → NoncompactSpace (Fin n → Fin M → AF F ⊗[F] E)) := by
  intro F E _ _ _ _ _ σ h n M
  obtain ⟨⟨C, hCc, hCy⟩, hfin, hnc⟩ := scalar F E σ h
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => C,
      isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hCc, ?_⟩
    intro y
    choose X hX using fun a i => hCy (y a i)
    exact ⟨X, fun a _ i _ => hX a i⟩
  · intro C hCc
    have hcont : ∀ a i, Continuous fun Y : Fin n → Fin M → AF F ⊗[F] E => Y a i :=
      fun a i => (continuous_apply i).comp (continuous_apply a)
    have hS : ∀ a i, {e : E | inclR (AF F) e ∈ (fun Y : Fin n → Fin M → AF F ⊗[F] E => Y a i) '' C}.Finite :=
      fun a i => hfin _ (hCc.image (hcont a i))
    refine (Set.Finite.pi fun a => Set.Finite.pi (hS a)).subset ?_
    intro X hX a _ i _
    exact ⟨ratTup (AF F) X, hX, rfl⟩
  · intro hn hM
    refine ⟨fun hK => hnc.noncompact_univ ?_⟩
    have hsurj : Function.Surjective fun Y : Fin n → Fin M → AF F ⊗[F] E => Y ⟨0, hn⟩ ⟨0, hM⟩ :=
      fun r => ⟨fun _ _ => r, rfl⟩
    have hc : Continuous fun Y : Fin n → Fin M → AF F ⊗[F] E => Y ⟨0, hn⟩ ⟨0, hM⟩ :=
      (continuous_apply (⟨0, hM⟩ : Fin M)).comp (continuous_apply (⟨0, hn⟩ : Fin n))
    have := hK.image hc
    rwa [Set.image_univ, hsurj.range_eq] at this

end GlobalTheory.CompanionTheory.SW.CocW
