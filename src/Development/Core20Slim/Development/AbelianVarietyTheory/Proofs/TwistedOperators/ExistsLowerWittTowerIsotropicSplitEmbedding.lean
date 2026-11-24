module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.LoweredSignatureVanishing
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankOrth
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.SignCompatibleNumberingOfWittTowerLower
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFrameOfHasSignature
public import Batteries.Classes.RatCast
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.MemberDatumOfFlagTie
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.SpanPowerMembership.Spaces
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Formalism.RealPlaceAnalysis.Complexify
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.SignatureConjugationInvariant
public import Formalism.SatakeDualWeyl.Statement
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Function
public import Init.Data.Int.Basic
public import Init.Data.Int.Lemmas
public import Init.Data.Int.Order
public import Init.Data.List.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Ext
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Filter
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.InvariantBasisNumber
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.SesquilinearForm.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Fin.Basic
public import Mathlib.Order.Monotone.Basic
public import Mathlib.Order.Monotone.Defs
public import Mathlib.RingTheory.FiniteType

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TowerSplit

theorem signCard_of_isEnum {n : ℕ} {S : SPar} {lam : Fin n → ℝ} {ε : Fin n → Bool} (h : IsEnum S lam ε) (b : Bool) :
    GlobalTheory.IndefiniteRowSideFullHecke.LoweredSignatureVanishing.signCard S b = (Finset.univ.filter fun a => ε a = b).card := by
  obtain ⟨hl, q, hq, rfl⟩ := h
  have hinj : Function.Injective q := fun a c hac => hl.injective (by rw [hq, hq, hac])
  unfold GlobalTheory.IndefiniteRowSideFullHecke.LoweredSignatureVanishing.signCard
  rw [Finset.filter_image, Finset.card_image_of_injective]
  intro a c hac
  exact hinj (Prod.ext_iff.1 hac).1

theorem hasSignature_of_model {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau) :
    Formalism.UG.HasSignature (gramAt D V τ) (GlobalTheory.IndefiniteRowSideFullHecke.LoweredSignatureVanishing.signCard (S τ) true)
      (GlobalTheory.IndefiniteRowSideFullHecke.LoweredSignatureVanishing.signCard (S τ) false) := by
  rw [signCard_of_isEnum (M.enum τ), signCard_of_isEnum (M.enum τ)]
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  have h1 : M.fr τ * (M.fr τ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hd
  refine GlobalTheory.AutInhab.hasSignature_of_frame (P := (M.fr τ)⁻¹) ?_ ?_
  · exact IsUnit.of_mul_eq_one _ (Matrix.nonsing_inv_mul _ hd)
  · rw [← M.fr_gram τ, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← conjTranspose_mul, h1, conjTranspose_one,
      Matrix.one_mul, Matrix.mul_assoc, h1, Matrix.mul_one]

theorem exists_isoSplit : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (_M : DSModel V S) (r : ℕ)
    (C : Matrix (Fin V.rank) (Fin r) D.host.E), IsIsoFrame V C →
    ∃ (V' : HSp D) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B ∧
      GlobalTheory.IndefiniteRowSideFullHecke.LoweredSignatureVanishing.SigLowered S r V' := by
  intro D V S M r C hC
  obtain ⟨e, rfl⟩ := GlobalTheory.BesselCompare.eMat_surj V C
  have he : LinearIndependent D.host.E e :=
    LinearIndependent.of_comp V.frame.equivFun.toLinearMap hC.2.1
  have hiso : ∀ a b, V.hT (e a) (e b) = 0 := fun a b => by
    rw [← GlobalTheory.BesselCompare.cT_mul, hC.2.2]; rfl
  obtain ⟨V', ι, h1, h2, h3⟩ := GlobalTheory.WittLow.exists_lower Examples₂.star_isIntegral V e he hiso
  have hlow : IsWittLower V V' r := by
    refine ⟨h1, ι, h2, _, ⟨hC.2.1, hC.2.2⟩, ?_⟩
    refine Matrix.ext fun a b => ?_
    rw [GlobalTheory.BesselCompare.frameMat_eq, GlobalTheory.BesselCompare.cT_mul]
    exact h3 _ _
  refine ⟨V', frameMat V V' ι, ⟨hC, ?_, ?_, by omega⟩, fun τ => ?_⟩
  · refine Matrix.ext fun a b => ?_
    unfold adj
    rw [GlobalTheory.BesselCompare.frameMat_eq, GlobalTheory.BesselCompare.cT_mul]
    exact h2 _ _
  · refine Matrix.ext fun a b => ?_
    unfold adj
    rw [GlobalTheory.BesselCompare.frameMat_eq, GlobalTheory.BesselCompare.cT_mul, ← V.herm.eq, h3]
    simp
  · obtain ⟨s, hs⟩ := GlobalTheory.WittLow.exists_sig V' (tauE D τ)
    have hs' : Formalism.UG.HasSignature (gramAt D V' τ) s.1 s.2 := hs
    obtain ⟨e1, e2⟩ := Formalism.UG.P.signature_unique _ _ _ _ _ _ (GlobalTheory.WittSign.hasSignature_of_isWittLower hlow τ hs')
      (hasSignature_of_model M τ)
    exact ⟨s.1, s.2, e1, e2, hs'⟩

end GlobalTheory.TowerSplit

end
