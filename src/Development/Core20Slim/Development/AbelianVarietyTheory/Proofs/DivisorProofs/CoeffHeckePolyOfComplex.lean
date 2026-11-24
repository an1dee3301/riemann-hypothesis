module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinPartConjMem
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeElementComponentMemStandardDoubleCoset
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotentsStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvolutionSphericalHeckeAntiStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlacesStatement
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.HeckeThetaElements.IsHeckeElt
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.NTheta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Bridge Polynomial
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeckeParts

variable {D : D7} {V : HSp D}

section Tr

variable {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {κ : GA D V}






variable {S : D.what₂.Tau → SPar} {M : DSModel V S}


end Tr

section Loc

variable {β : GL (Fin V.rank) (Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} {N : ℕ}
  {L : LevDat D.host.E ℂ V.rank}

def OffLevel (L : LevDat D.host.E ℂ V.rank) (N : ℕ) (P : Pl D.host.E) : Prop :=
  Formalism.HermitianLatticesTheory.conjIdeal (K := D.host.E) P.asIdeal ≠ P.asIdeal ∧ ((N : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal ∧
    ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → PP ≠ P ∧ ¬ IsConjPl PP P

def LocRep (J : Subgroup (GA D V)) (P : Pl D.host.E) (x : GA D V) (A : Finset (GA D V)) : Prop :=
  (∃ e, IsIdemAt e P ∧ SuppAt e V x ∧ ∀ a ∈ A, SuppAt e V a) ∧ IsDC J x A


theorem idem_unique (V : HSp D) {P : Pl D.host.E} {e e' : Formalism.L2.Theta.AE D} (he : IsIdemAt e P) (he' : IsIdemAt e' P) : e' = e :=
  (((GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents V).2.2.1 P e _ (Or.inl ⟨he, rfl⟩)).2.2.2.1 e' _ (Or.inl ⟨he', rfl⟩)).1









end Loc

section Model

variable {β : GL (Fin V.rank) (Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} {N : ℕ}
  {L : LevDat D.host.E ℂ V.rank} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)}
  {S : D.what₂.Tau → SPar} {M : DSModel V S}



variable {μ : Measure (GA D V)} {𝓕 : Set (GA D V)} {HM : HMod (MMap M)} {U : Submodule ℂ (MMap M)} {c : ℂ}




variable {Pl0 : Type} {ok : Set Pl0} {pl : Pl0 → Pl D.host.E} {q : Pl0 → ℕ}

end Model

section Parts


variable {β : GL (Fin V.rank) (Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} {N : ℕ}
  {L : LevDat D.host.E ℂ V.rank} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)}
  {S : D.what₂.Tau → SPar} {M : DSModel V S}
  {μ : Measure (GA D V)} {𝓕 : Set (GA D V)} {HM : HMod (MMap M)} {U : Submodule ℂ (MMap M)} {c : ℂ}
  {Pl0 : Type} {ok : Set Pl0} {pl : Pl0 → Pl D.host.E} {q : Pl0 → ℕ}

variable (hβ : IsBaseFrame V β Λ N) (hok : ∀ P ∈ ok, OffLevel L N (pl P))
  (hχ : ∀ k ∈ levG V β L, levChi V β L k = 1) (hμ : μ.IsHaarMeasure) (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 μ)
  (h : HM.Is U fun T T' => c * ipM M μ 𝓕 T T') (hU : U ≤ Mult θ M (levS V β L) (levChi V β L))
  (hst : ∀ P ∈ ok, ∀ x A, LocRep (levG V β L) (pl P) x A → ∀ T ∈ U, heckeOn M A T ∈ U) (hq : ∀ P ∈ ok, q P ≠ 0)

include hβ hok hχ hμ h𝓕 h hU hst hq

end Parts

end GlobalTheory.HeckeParts

end
