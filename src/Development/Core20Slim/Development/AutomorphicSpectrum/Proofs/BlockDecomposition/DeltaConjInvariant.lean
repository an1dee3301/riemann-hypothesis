module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaPartD
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundUnitary
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermInf
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermOf
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FiniteAdeleTopologyStatement
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RatTuple
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.GlobalProofs.SchwartzBruhatEqSumPure
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.GlobalProofs.AdelicCharacterArchimedeanFormStatement
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.StandardAdelicCharacterStatement
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteAdeleHaarMapEqScaledVolumeStatement
public import Init.Core
public import Init.Data.Function
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.PropLemmas
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.Hom.Rat
public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.GroupTheory.Index
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Logic.Function.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal

@[expose] public section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
open NumberField
open GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl GlobalTheory.CompanionTheory.SW.Core

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.DeltaMap

theorem bijective_algHom (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E) : Function.Bijective σ := by
  have hinj : Function.Injective σ := (σ : E →+* E).injective
  refine ⟨hinj, ?_⟩
  let τ : E →ₐ[ℚ] E := (σ : E →+* E).toRatAlgHom
  have h2 : Function.Injective τ.toLinearMap := hinj
  exact LinearMap.injective_iff_surjective.mp h2

theorem delta_map (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (n : ℕ) (c : Matrix (Fin n) (Fin n) E) : delta (c.map σ) = delta c := by
  classical
  let e : E ≃+* E := (AlgEquiv.ofBijective σ (bijective_algHom F E σ)).toRingEquiv
  let ψ : 𝓞 E ≃+* 𝓞 E := NumberField.RingOfIntegers.mapRingEquiv e
  have hψ : ∀ o : 𝓞 E, algebraMap (𝓞 E) E (ψ o) = σ (algebraMap (𝓞 E) E o) := fun o => rfl
  let φ : (Fin n → 𝓞 E) →+ (Fin n → 𝓞 E) :=
    { toFun := fun y i => ψ (y i)
      map_zero' := by
        funext i
        simp
      map_add' := by
        intro y z
        funext i
        simp }
  have hφ : ∀ y j, φ y j = ψ (y j) := fun y j => rfl
  have hvec : ∀ y : Fin n → 𝓞 E, (c.map σ) *ᵥ (fun j => algebraMap (𝓞 E) E (φ y j)) =
      fun i => σ ((c *ᵥ fun j => algebraMap (𝓞 E) E (y j)) i) := by
    intro y
    funext i
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul, hφ, hψ]
  have key : Kc c = (Kc (c.map σ)).comap φ := by
    ext y
    rw [AddSubgroup.mem_comap]
    show (∀ i, ∃ o : 𝓞 E, algebraMap (𝓞 E) E o = (c *ᵥ fun j => algebraMap (𝓞 E) E (y j)) i) ↔
      (∀ i, ∃ o : 𝓞 E, algebraMap (𝓞 E) E o = ((c.map σ) *ᵥ fun j => algebraMap (𝓞 E) E (φ y j)) i)
    rw [hvec]
    refine forall_congr' fun i => ⟨fun h => h.elim fun o ho => ⟨ψ o, by rw [hψ, ho]⟩,
      fun h => h.elim fun o ho => ⟨ψ.symm o, ?_⟩⟩
    apply e.injective
    show σ (algebraMap (𝓞 E) E (ψ.symm o)) = σ _
    rw [← hψ, RingEquiv.apply_symm_apply, ho]
  have hsurj : Function.Surjective φ := fun y =>
    ⟨fun i => ψ.symm (y i), funext fun i => ψ.apply_symm_apply (y i)⟩
  show (Kc (c.map σ)).index = (Kc c).index
  rw [key]
  first
    | exact (AddSubgroup.index_comap_of_surjective hsurj).symm
    | exact (AddSubgroup.index_comap_of_surjective _ hsurj).symm
    | exact (AddSubgroup.index_comap_of_surjective (H := Kc (c.map σ)) hsurj).symm

end GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.DeltaMap
