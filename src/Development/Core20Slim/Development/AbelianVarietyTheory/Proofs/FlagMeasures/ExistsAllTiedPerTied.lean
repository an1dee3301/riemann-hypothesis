module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsBesPosOfBesselTied
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOpenKer
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BesselCharacterGenericCharacterLaws
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NEqAndIsClosed
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FlagMeasures.AnisotropicIteratedIntegrability
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueNormalizedHaarMeasureAdelicUnitary
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsClosedNFlag
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryUnimodularExistsFundamentalDomain
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitOfCocompact
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousAdelicUnitaryEmbedding
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedBessel
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Topology.Defs.Basic

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory IsDedekindDomain NumberField
open scoped TensorProduct

namespace GlobalTheory.Per.Inhab

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Iterated

variable {G N : Type} [MeasurableSpace G] [MeasurableSpace N] {μ : Measure G} {𝓕 : Set G} {ν : Measure N} {𝓝 : Set N}
  {P P' R : G → N → ℂ}


end Iterated

variable {D : D7}


section Invariant

variable {A B : HSp D} {ι : A.V →ₗ[D.host.E] B.V} {ρ : ℕ} {e : Matrix (Fin B.rank) (Fin ρ) D.host.E}

structure IsRatInv (ι : A.V →ₗ[D.host.E] B.V) (e : Matrix (Fin B.rank) (Fin ρ) D.host.E)
    (Q : GA D A → GA D B → ℂ) : Prop where
  norm : ∀ δ γ, EmbRel B A ι δ γ → ∀ n ∈ NFlag B e, δ * n * δ⁻¹ ∈ NFlag B e
  left : ∀ g, ∀ n ∈ NFlag B e, ∀ γ ∈ NFlag B e, γ ∈ GQ B → Q g (γ * n) = Q g n
  conj : ∀ g, ∀ n ∈ NFlag B e, ∀ γ ∈ GQ A, ∀ δ, EmbRel B A ι δ γ → Q (γ * g) (δ * n * δ⁻¹) = Q g n

variable {Q : GA D A → GA D B → ℂ}

end Invariant

section Integrands

variable {A B : HSp D} {ι : A.V →ₗ[D.host.E] B.V} {s : GA D A → GA D B} {φ : GA D A → ℂ} {F : GA D B → ℂ}


theorem emb_continuous (hι : HSpace.IsIsomEmb A B ι) (hs : ∀ h, EmbRel B A ι (s h) h) : Continuous s := by
  obtain ⟨s₀, hc, hrel, -⟩ := GlobalTheory.Mem.UnitaryEmb.exists_embHom D B A ι hι
  obtain rfl : s = s₀ := funext fun h => (hrel h _).1 (hs h)
  exact hc


end Integrands

section Periods

variable {X : ThetaX D} {T : ThetaTied D X} (Wl : WeilTied D X T) {A B : HSp D} {ι : A.V →ₗ[D.host.E] B.V}

structure IsGood (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) : Prop where
  sigOK : A.SigOK
  aniso : IsAniso A
  rank : 1 < A.rank
  isom : HSpace.IsIsomEmb A B ι

structure Frame (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) {ρ : ℕ} (e : Matrix (Fin B.rank) (Fin ρ) D.host.E) where
  μ : Measure (GA D A)
  𝓕 : Set (GA D A)
  ν : Measure (NFlag B e)
  𝓝 : Set (NFlag B e)
  s : GA D A → GA D B
  vol : IsVolPair D A μ 𝓕
  unit : IsUnitN B e ν 𝓝
  emb : ∀ h, EmbRel B A ι (s h) h


section

variable {ρ : ℕ} {e : Matrix (Fin B.rank) (Fin ρ) D.host.E} {f f' f'' : Frame A B ι e → ℂ}

end

variable (hg : IsGood A B ι)

include hg

omit hg

end Periods

section Record

variable {X : ThetaX D} {T : ThetaTied D X}

variable (Wl : WeilTied D X T) {A B : HSp D} {ι : A.V →ₗ[D.host.E] B.V}

end Record

end GlobalTheory.Per.Inhab

end
