module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FlatSpaceComponents
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnramifiedOfIsCMUnram
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianSpacesSameSignatureIsometric
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.AdelicUnitaryGroups
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsCongrIffTraceFormsIsometricCm
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FiniteResidueFieldAdicCompletionIntegers
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasseNormTheoremQuadraticExtension
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLocalConjugationSelfDualLatticesHost
public import Development.AbelianVarietyTheory.PublishedTheorems.AdelicLattices₂.AlgebraMapNormOfBasisOneSqrt
public import Formalism.HermitianLattices.StatementLat
public import Formalism.HermitianLattices.StatementMass
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SatakeDualWeyl.Statement
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Classical
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.Lattice.Basic
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Rat.Defs
public import Mathlib.FieldTheory.Separable
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.LinearAlgebra.SesquilinearForm.Basic
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.CMField
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.FractionalIdeal.Basic
public import Mathlib.RingTheory.FractionalIdeal.Operations
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature
public import ReciprocityTheory.SemistableReduction.TorsionNonvanishStatement

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.RationalIsometry
open ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.SelfDualGenus GlobalTheory.LocalConjugacy

section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
attribute [local instance] IsCMField.starRing

theorem exists_congr (hc : Formalism.HermitianLatticesTheory.IsCMUnram E) {r : ℕ} {J J' : Matrix (Fin r) (Fin r) E}
    (hG : ∀ a b, cc (Jᵀ a b) = Jᵀ b a) (hG' : ∀ a b, cc (J'ᵀ a b) = J'ᵀ b a)
    (hd : J.det ≠ 0) (hd' : J'.det ≠ 0) {L L' : Submodule (𝓞 E) (Fin r → E)}
    (hL : ReciprocityTheory.MultiplicativeHeights.IsLattice L) (hL' : ReciprocityTheory.MultiplicativeHeights.IsLattice L')
    (hsd : ∀ x, x ∈ L ↔ ∀ y ∈ L, IsIntegral ℤ (herm Jᵀ x y))
    (hsd' : ∀ x, x ∈ L' ↔ ∀ y ∈ L', IsIntegral ℤ (herm J'ᵀ x y))
    (hs : ∀ τ : E →+* ℂ, ∃ p q, Formalism.UG.HasSignature (J.map τ) p q ∧ Formalism.UG.HasSignature (J'.map τ) p q) :
    ∃ P : Matrix (Fin r) (Fin r) E, P.det ≠ 0 ∧ ∀ x y, herm Jᵀ (P *ᵥ x) (P *ᵥ y) = herm J'ᵀ x y := by
  haveI := GlobalTheory.DefiniteMass.unramified_of_isCMUnram hc
  have hone : ∀ z : E, z ∈ (1 : FractionalIdeal (𝓞 E)⁰ E) ↔ IsIntegral ℤ z := fun z =>
    (FractionalIdeal.mem_one_iff _).trans ⟨fun ⟨a, ha⟩ => ha ▸ a.2, fun hz => ⟨⟨z, hz⟩, rfl⟩⟩
  obtain ⟨P, hP0, hP⟩ := congr_of_modular (G := Jᵀ) (G' := J'ᵀ) (L := L) (L' := L') (𝔟 := 1)
    (GlobalTheory.LocalQuad.landherr_of_hasseNormSt GlobalTheory.QNorm.hasseNormSt) GlobalTheory.QNorm.hasseNormSt one_ne_zero
    (fun z hz => by
      obtain ⟨a, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 hz
      exact (FractionalIdeal.mem_one_iff _).2 ⟨IsCMField.ringOfIntegersComplexConj E a, rfl⟩)
    hG hG' (by rwa [Matrix.det_transpose]) (by rwa [Matrix.det_transpose]) hL hL'
    (by simpa only [hone] using hsd) (by simpa only [hone] using hsd')
    (fun τ => by
      obtain ⟨p, q, h, h'⟩ := hs τ
      obtain ⟨f⟩ : Nonempty (Fin r ≃ Fin p ⊕ Fin q) := ⟨h.choose⟩
      obtain ⟨A, hA, e⟩ := GlobalTheory.FlagMeas.exists_congr_of_hasSignature h f
      obtain ⟨A', hA', e'⟩ := GlobalTheory.FlagMeas.exists_congr_of_hasSignature h' f
      refine GlobalTheory.Published.Landherr.congr_of_gram_eq τ hA hA' ?_
      rw [GlobalTheory.Published.gram_eq, GlobalTheory.Published.gram_eq]
      exact e.trans e'.symm)
  exact ⟨P, hP0, fun x y => by rw [herm_mulVec, ← hP]⟩

theorem gram_herm (W : HSpace E) (a b : Fin W.rank) : cc (W.gramᵀ a b) = W.gramᵀ b a :=
  W.herm.eq (W.frame b) (W.frame a)

theorem exists_isometry (hc : Formalism.HermitianLatticesTheory.IsCMUnram E) (W Y : HSpace E) (hW : W.SigOK) (hY : Y.SigOK)
    (hr : W.rank = Y.rank) (hs : ∀ τ, W.sig τ = Y.sig τ) :
    ∃ φ : W.V ≃ₗ[E] Y.V, HSpace.IsIsomEmb W Y φ.toLinearMap := by
  obtain @⟨V, i1, i2, i3, i4, i5, hT, hh, hn, r, hrk, fr, sg, L, hL, hu⟩ := Y
  change W.rank = r at hr
  subst hr
  let Y : HSpace E := ⟨V, hT, hh, hn, W.rank, hrk, fr, sg, L, hL, hu⟩
  obtain ⟨P, hP0, hP⟩ := exists_congr hc (r := W.rank) (J := Y.gram) (J' := W.gram) (gram_herm Y) (gram_herm W)
    (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.gram_det_isUnit Y).ne_zero (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.gram_det_isUnit W).ne_zero
    (isLattice_coordLat Y Y.L0 Y.standardTuple_isLattice Y.baseLattice_isUnimodular)
    (isLattice_coordLat W W.L0 W.standardTuple_isLattice W.baseLattice_isUnimodular)
    (selfDual_coordLat Y Y.L0 Y.baseLattice_isUnimodular) (selfDual_coordLat W W.L0 W.baseLattice_isUnimodular)
    (fun τ => ⟨_, _, hY τ, by have := hW τ; rwa [hs τ] at this⟩)
  refine ⟨(W.frame.equivFun.trans (Matrix.toLinearEquiv' P (Matrix.invertibleOfIsUnitDet P hP0.isUnit))).trans
    Y.frame.equivFun.symm, fun x y => ?_⟩
  change Y.hT (Y.frame.equivFun.symm (P *ᵥ W.frame.equivFun x))
    (Y.frame.equivFun.symm (P *ᵥ W.frame.equivFun y)) = _
  rw [← herm_coord, ← herm_coord, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  exact hP _ _

end

theorem rationalSt (D : D7) : GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.RationalSt D :=
  haveI : IsCMField D.host.E := D.host.isCMField_hostE
  fun W Y hW hY hr hs => exists_isometry (E := D.host.E) D.sp.cm.cmUnram W Y hW hY hr hs

end GlobalTheory.RationalIsometry

end
