module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.Divisibility.DefGroupLemmas
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.AfsplitB
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralChangeBaseFrameOrthonormal
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParahoricLevelLiftsExist
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentPreservesLatticeHat
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.HeckeThetaElements.IsHeckeElt
public import Formalism.LocalToGlobal.HermitianColumns.InLocalDiscriminantKernel
public import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Cast
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR.Lev Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV 
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinAdIdent

section Generic

variable {R : Type} [CommRing R] {m n : ℕ} {J : Matrix (Fin m) (Fin n) R} {J' : Matrix (Fin n) (Fin m) R}
  {M : Matrix (Fin n) (Fin n) R} {M' : Matrix (Fin m) (Fin m) R}





end Generic

section Red

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}


end Red

variable {D : D7}


def Good (N : ℕ) (f : Af D.host.F ⊗[D.host.F] D.host.E) : Prop :=
  f * f = f ∧ ∃ u : Formalism.L2.Herm.intAf D.host.F D.host.E, (u : EAf D) * (N : EAf D) = swapAE D f





section Away

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]





end Away



set_option maxHeartbeats 800000 in
theorem lamHat_good {V : HSp D} {β : GL (Fin V.rank) (EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} {N : ℕ}
    (hB : IsBaseFrame V β Λ N) {f : Af D.host.F ⊗[D.host.F] D.host.E} (hf : Good N f) :
    (∀ y ∈ Formalism.L2.NTheta.LamHat V, f • y ∈ Formalism.L2.NTheta.LamHat V) ∧
      ∀ y, f • y ∈ Formalism.L2.NTheta.LamHat V ↔ (fun a => swapAE D (f * y a)) ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ := by
  obtain ⟨-, -, -, h01, h10⟩ := hB
  obtain ⟨hff, u, hu⟩ := hf
  have key : ∀ z, z ∈ Formalism.L2.NTheta.LamHat V ↔
      (fun i => swapAE D (z i)) ∈ Formalism.L2.Herm.hatL (F := D.host.F) (GlobalTheory.LevSplit.L0sub V) :=
    fun z => GlobalTheory.LevSplit.latHat_iff (GlobalTheory.LevSplit.L0sub V) z
  have hε : swapAE D f * swapAE D f = swapAE D f := by rw [← RingHom.map_mul, hff]
  have hsw : ∀ y : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E,
      (fun a => swapAE D (f * y a)) = fun a => swapAE D f * swapAE D (y a) := fun y => funext fun a => RingHom.map_mul _ _ _
  have a01 := GlobalTheory.LevSplit.hatL_smul (F := D.host.F) (GlobalTheory.LevSplit.L0sub V) Λ N h01
  have a10 := GlobalTheory.LevSplit.hatL_smul (F := D.host.F) Λ (GlobalTheory.LevSplit.L0sub V) N h10
  obtain ⟨φ, hφ⟩ : ∃ φ : Formalism.L2.Herm.intAf D.host.F D.host.E, (φ : EAf D) = swapAE D f := ⟨u * N, hu⟩
  refine ⟨fun y hy => (key _).2 ?_, fun y => (key _).trans ?_⟩
  · show (fun a => swapAE D (f * y a)) ∈ _
    rw [hsw, ← hφ]
    exact Submodule.smul_mem _ φ ((key y).1 hy)
  · show (fun a => swapAE D (f * y a)) ∈ _ ↔ _
    rw [hsw]
    exact ⟨GlobalTheory.LatLoc.loc_transfer _ _ N u _ hu hε a01 _, GlobalTheory.LatLoc.loc_transfer _ _ N u _ hu hε a10 _⟩

end GlobalTheory.FinAdIdent

end
