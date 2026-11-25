module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.RationalRayLevels
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeCharEqOneOfTrivialFinitePartOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsNthRootIdeleFinitePartOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdelicCharacterPowEqOneFiniteIdelesOfOrderDvd
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
  Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwistFinPart



theorem exists_isDetRoot_finPart_one {D : D7} (V : HSp D) (a : GA D V) (ha : finHom V a = 1) (z : (AE D)ˣ)
    (hz : IsDetRoot V a z) : ∃ y : (AE D)ˣ, finPart D (y : AE D) = 1 ∧ IsDetRoot V a y := by
  obtain ⟨y, hyi, hyf⟩ := GlobalTheory.PlaceIdem.parts_surj D (infPart D (z : AE D)) 1
  obtain ⟨y', hyi', hyf'⟩ := GlobalTheory.PlaceIdem.parts_surj D (infPart D ((z⁻¹ : (AE D)ˣ) : AE D)) 1
  have hyy : y * y' = 1 := GlobalTheory.PlaceIdem.parts_inj D _ _
    (by rw [RingHom.map_mul, hyi, hyi', ← RingHom.map_mul, Units.mul_inv, RingHom.map_one])
    (by rw [RingHom.map_mul, hyf, hyf', mul_one, RingHom.map_one])
  have hc : ∀ w : AE D, infPart D (sigR (AF D.host.F) D.sp.cm.sig w) =
      sigR (Ainf D.host.F) D.sp.cm.sig (infPart D w) := fun w => GlobalTheory.PlaceIdem.infPart_cA D w
  have hf : ∀ w : AE D, finPart D (sigR (AF D.host.F) D.sp.cm.sig w) =
      sigR (Af D.host.F) D.sp.cm.sig (finPart D w) := fun w => GlobalTheory.PlaceIdem.finPart_cA D w
  have e2 : finPart D (matHom V a).1.det = 1 := by
    have e : finPart D (matHom V a).1.det = (finHom V a).1.det := (finPart D).map_det _
    rw [e, ha]
    simp
  refine ⟨⟨y, y', hyy, by rw [mul_comm]; exact hyy⟩, hyf, ?_⟩
  show y = (matHom V a).1.det * sigR (AF D.host.F) D.sp.cm.sig y
  refine GlobalTheory.PlaceIdem.parts_inj D _ _ ?_ ?_
  · have h1 := congrArg (infPart D) hz
    unfold IsDetRoot at h1
    rw [RingHom.map_mul, hc] at h1
    rw [RingHom.map_mul, hc, hyi]
    exact h1
  · rw [RingHom.map_mul, hf, hyf, e2, RingHom.map_one, one_mul]



end GlobalTheory.TwistFinPart
