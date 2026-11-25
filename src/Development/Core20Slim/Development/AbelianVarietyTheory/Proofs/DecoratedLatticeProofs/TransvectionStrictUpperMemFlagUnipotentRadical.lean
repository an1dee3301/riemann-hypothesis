module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerBF
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BesselCharacterGenericCharacterLaws
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompProjAnisotropicAnisotropicEmbedding
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryTransvectionUnitaryAndConjugation
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedBessel
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SatakeDualWeyl.Statement
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Pi
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Notation.Pi.Basic
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.TransvFlag

open GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction

theorem form_vecX {D : D7} {V V₀ : HSp D} {ρ : ℕ} (d : HypDec V V₀ ρ) (b : Fin ρ → AE D) (y : VA V) :
    form V y (vecX d b) = (fun i => cA D (b i)) ⬝ᵥ (d.pY *ᵥ y) := by
  have h1 : (fun i => cA D (vecX d b i)) = (d.jX.map (cA D)) *ᵥ (fun i => cA D (b i)) := by
    funext i
    exact RingHom.map_mulVec (cA D) d.jX b i
  rw [form, h1, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec]
  have hp : d.pY = adj d.jX * gA V := by
    rw [HypDec.pY, HypDec.qY, HypDec.jX, gA, ← rat_conjTranspose]
    exact Matrix.map_mul
  conv_rhs => rw [hp, ← Matrix.mulVec_mulVec]
  rfl

theorem mul_eq_of_cols {R : Type} [CommRing R] {n ρ : ℕ} (M : Matrix (Fin n) (Fin n) R) (E : Matrix (Fin n) (Fin ρ) R)
    (T : Matrix (Fin ρ) (Fin ρ) R)
    (h : ∀ k, M *ᵥ (E *ᵥ Pi.single k 1) = E *ᵥ Pi.single k 1 + E *ᵥ (fun i => T i k)) : M * E = E + E * T := by
  refine Matrix.ext_of_mulVec_single fun k => ?_
  rw [← Matrix.mulVec_mulVec, Matrix.add_mulVec, ← Matrix.mulVec_mulVec, Matrix.mulVec_single_one T k, h k]
  rfl

theorem transv_mem_flagN : ∀ (D : D7) (V V₀ : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (b : Fin ρ → AE D)
    (v : GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.VA V),
    (∀ i k : Fin ρ, k ≤ i → GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.form V (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.vecX d (Pi.single k 1)) v * b i = 0) →
    ∀ u : GA D V, GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.IsTransv V (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.vecX d b) v u → u ∈ flagN d := by
  intro D V V₀ ρ d b v hb u hu
  unfold flagN
  rw [GlobalTheory.BesselChar.mem_NFlag_iff V d.e (isIsoSub_e d).1]
  have hperp : ∀ y : VA V, d.pY *ᵥ y = 0 → act V u y = y + d.jX *ᵥ (form V y v • b) := by
    intro y hy
    rw [hu y, transv, form_vecX, hy, dotProduct_zero, zero_smul, sub_zero, mul_zero, zero_smul, sub_zero,
      Matrix.mulVec_smul]
    rfl
  refine ⟨⟨Matrix.of fun i k => form V (vecX d (Pi.single k 1)) v * b i, fun j i hij => hb j i hij, ?_⟩,
    fun y hy => ⟨form V y v • b, hperp y hy⟩⟩
  have e1 : d.e.map (incA D) = d.jX := rfl
  rw [e1]
  refine mul_eq_of_cols _ _ _ fun k => ?_
  have hp : d.pY * d.jX = 0 := by
    have h := congrArg rat d.ee
    rw [rat_zero] at h
    rw [HypDec.pY, HypDec.qY, HypDec.jX]
    simpa only [rat, Matrix.map_mul] using h
  have hk : d.pY *ᵥ vecX d (Pi.single k 1) = 0 := by
    rw [vecX, Matrix.mulVec_mulVec, hp, Matrix.zero_mulVec]
  exact hperp _ hk

end GlobalTheory.TransvFlag
