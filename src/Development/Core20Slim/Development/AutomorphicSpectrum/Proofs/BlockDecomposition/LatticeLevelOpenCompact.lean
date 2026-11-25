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
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FiniteAdeleTopology
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Operations
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Free
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.Homeomorph.Lemmas

@[expose] public section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
open NumberField
open GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl GlobalTheory.CompanionTheory.SW.Core

noncomputable section
namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl

theorem latN_isOpen_isCompact : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (n M N : ℕ), 0 < N →
    IsOpen (latN b n M N : Set (Fin n → Fin M → Af F ⊗[F] E)) ∧
    IsCompact (latN b n M N : Set (Fin n → Fin M → Af F ⊗[F] E)) := by
  intro F E _ _ _ _ _ σ _ d b n M N hN
  have hNF : (N : F) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hN)
  obtain ⟨u, hu⟩ : IsUnit (N : Af F) := by
    have h1 : IsUnit (algebraMap F (Af F) (N : F)) := (IsUnit.mk0 _ hNF).map _
    rwa [map_natCast] at h1
  have hSo : IsOpen {y : Af F | ∃ z ∈ Oh F, y = (N : Af F) * z} := by
    have hpre : {y : Af F | ∃ z ∈ Oh F, y = (N : Af F) * z} = (fun y => (↑u⁻¹ : Af F) * y) ⁻¹' Oh F := by
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        show (↑u⁻¹ : Af F) * ((N : Af F) * z) ∈ Oh F
        rw [← hu, ← mul_assoc, Units.inv_mul, one_mul]
        exact hz
      · intro hy
        exact ⟨(↑u⁻¹ : Af F) * y, hy, by rw [← hu, ← mul_assoc, Units.mul_inv, one_mul]⟩
    rw [hpre]
    exact (AfTop.isOpen_Oh F).preimage (continuous_const_mul _)
  have hSc : IsCompact {y : Af F | ∃ z ∈ Oh F, y = (N : Af F) * z} := by
    have himg : {y : Af F | ∃ z ∈ Oh F, y = (N : Af F) * z} = (fun z => (N : Af F) * z) '' Oh F := by
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact ⟨z, hz, rfl⟩
      · rintro ⟨z, hz, rfl⟩
        exact ⟨z, hz, rfl⟩
    rw [himg]
    exact (AfTop.isCompact_Oh F).image (continuous_const_mul _)
  haveI : IsModuleTopology (Af F) (Af F ⊗[F] E) := ⟨rfl⟩
  let Bs := Algebra.TensorProduct.basis (Af F) b
  let e : (Af F ⊗[F] E) ≃ₜ (Fin d → Af F) :=
    { Bs.equivFun.toEquiv with
      continuous_toFun := IsModuleTopology.continuous_of_linearMap Bs.equivFun.toLinearMap
      continuous_invFun := IsModuleTopology.continuous_of_linearMap Bs.equivFun.symm.toLinearMap }
  have hT : {x : Af F ⊗[F] E | InNOh b N x} =
      e ⁻¹' Set.univ.pi (fun _ => {y : Af F | ∃ z ∈ Oh F, y = (N : Af F) * z}) := by
    ext x
    rw [Set.mem_preimage, Set.mem_univ_pi]
    exact Iff.rfl
  have hlat : (latN b n M N : Set (Fin n → Fin M → Af F ⊗[F] E)) =
      Set.univ.pi (fun _ => Set.univ.pi (fun _ => {x : Af F ⊗[F] E | InNOh b N x})) := by
    ext X
    simp only [Set.mem_univ_pi]
    exact Iff.rfl
  have hTo : IsOpen {x : Af F ⊗[F] E | InNOh b N x} := by
    rw [hT]
    exact (isOpen_set_pi Set.finite_univ fun _ _ => hSo).preimage e.continuous
  have hTc : IsCompact {x : Af F ⊗[F] E | InNOh b N x} := by
    rw [hT]
    exact e.isCompact_preimage.mpr (isCompact_univ_pi fun _ => hSc)
  rw [hlat]
  exact ⟨isOpen_set_pi Set.finite_univ fun _ _ => isOpen_set_pi Set.finite_univ fun _ _ => hTo,
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hTc⟩

end GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl
