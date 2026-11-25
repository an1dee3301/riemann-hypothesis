module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormPeriodSq
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Hilbert90IntegralIdelesOfMovedPrimes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicUnitaryCharacterTrivialAtNonsplitPlace
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardLatticeDoubleCosetClassesStabilisers
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPrimeIffNonSplitPlaceIdempotent
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAdelicPointUnitaryGroupGramOne
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepLatticeStabilizerVacuumEqDetCharSmul
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaCosetIndicatorReadingSphericalOffModulus
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePartRationalTensorZeroAtPrimeIffPlaceIdem
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardLatticeSelfDualAndIntegralIffStabilizes
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalVolumeLift
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitaryOnTheta
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodModModT
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.HermitianColumns.InLocalDiscriminantKernel
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Classical
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Ext
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

open NumberField IsDedekindDomain
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open scoped TensorProduct Matrix

namespace GlobalTheory.InertLocalPoint

open GlobalTheory.BotClassDict GlobalTheory.NormRatio GlobalTheory.NormRatio.StdLevel

theorem idem_mul_idem {D : D7} {v w : HeightOneSpectrum (𝓞 D.host.F)} {ε η : AF D.host.F}
    (hε : IsPlaceIdem D v ε) (hη : IsPlaceIdem D w η) (hne : w ≠ v) : η * ε = 0 := by
  obtain ⟨α, rfl, -, h0⟩ := hε
  obtain ⟨β, rfl, -, k0⟩ := hη
  refine Prod.ext (zero_mul (0 : Ainf D.host.F)) (FiniteAdeleRing.ext _ fun u => ?_)
  change β u * α u = 0
  by_cases hu : u = v
  · have : β u = 0 := k0 u (hu ▸ hne.symm)
    rw [this, zero_mul]
  · have : α u = 0 := h0 u hu
    rw [this, mul_zero]

theorem suppInert_finStd {D : D7} (V : HSp D) (hG : V.gram = 1) {v : HeightOneSpectrum (𝓞 D.host.F)}
    {ε : AF D.host.F} (hv : GlobalTheory.WeilParts.NonSplitAt D v ε) {g : GA D V} (hg : GlobalTheory.WeilParts.SuppPl ε V g) :
    Formalism.MainNotions.StandardLatticesGL3.SuppInert D (finStd V hG g : GL (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) := by
  intro q hq hnI i j
  have e : ((finStd V hG g : GL (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) i j -
      (1 : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) i j = finQ D ((Formalism.L2.Theta.mt V g - 1) i j) := by
    rw [Matrix.sub_apply, RingHom.map_sub, finStd_apply]
    congr 1
    rw [Matrix.one_apply, Matrix.one_apply]
    split_ifs
    · exact (RingHom.map_one _).symm
    · exact (RingHom.map_zero _).symm
  rw [e]
  refine (GlobalTheory.ZeroAtPlaces.zeroAt_finQ_iff D q hq _).2 fun w η hη hqw => ?_
  have hne : w ≠ v := by
    rintro rfl
    exact hnI ((GlobalTheory.InertPlace.inertQ_iff_nonSplitAt D q hq w ε hv.1 hqw).2 hv)
  rw [← hg i j, ← mul_assoc, ← map_mul, idem_mul_idem hv.1 hη hne, map_zero, zero_mul]

theorem intG_finStd {D : D7} (V : HSp D) (hG : V.gram = 1) {g : GA D V}
    (h : ∀ y : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E,
      y ∈ Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E ((Formalism.MainNotions.StandardLatticesGL3.stdL D V.rank : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) :
        Set (Fin V.rank → D.host.E)) ↔
      (Formalism.MainNotions.StandardLattice.finMat D.sp.cm.sig V.gram g).mulVec y ∈ Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E
        ((Formalism.MainNotions.StandardLatticesGL3.stdL D V.rank : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) : Set (Fin V.rank → D.host.E))) :
    Formalism.MainNotions.StandardLatticesGL3.IntG D (finStd V hG g : GL (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) := by
  have e1 : ∀ (k : GA D V) (i j : Fin V.rank),
      (((finStd V hG k : Formalism.MainNotions.StandardLatticesGL3.GA D V.rank) : GL (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) :
        Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) i j ∈ Formalism.MainNotions.StandardLatticesGL3.OhE D ↔
        (finHom V k).1 i j ∈ intAE D := fun k i j => by
    rw [← toAfE_int_iff, toAfE_finStd, mem_intAE_iff_swap]
  have e2 : ((↑(finStd V hG g) : GL (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D))⁻¹ : GL (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) =
      ↑(finStd V hG g⁻¹) := by rw [map_inv, Subgroup.coe_inv]
  have hR : ∀ y : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E,
      (∀ i, y i ∈ intSub D) ↔ ∀ i, ((finHom V g).1 *ᵥ y) i ∈ intSub D := fun y =>
    (mem_latHat_stdLat V y).symm.trans ((h y).trans (mem_latHat_stdLat V _))
  have h1 : (finHom V g).1 * (finHom V g⁻¹).1 = 1 := by
    rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
  have h2 : (finHom V g⁻¹).1 * (finHom V g).1 = 1 := by
    rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
  obtain ⟨ha, hb⟩ := (preserves_iff (intSub D) _ _ h1 h2).1 hR
  intro i j
  rw [e2]
  exact ⟨(e1 g i j).2 (ha i j), (e1 g⁻¹ i j).2 (hb i j)⟩

theorem suppInert_and_intG : ∀ {D : Formalism.BasicNotions.D7} (V : Formalism.BasicNotions.TH.HSp D) (hG : V.gram = 1) (v : HeightOneSpectrum (𝓞 D.host.F)) (ε : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F), GlobalTheory.WeilParts.NonSplitAt D v ε → ∀ g : Formalism.L2.Theta.GA D V, GlobalTheory.WeilParts.SuppPl ε V g → (∀ y : Fin V.rank → TensorProduct D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.host.E, y ∈ Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E ((Formalism.MainNotions.StandardLatticesGL3.stdL D V.rank : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) : Set (Fin V.rank → D.host.E)) ↔ (Formalism.MainNotions.StandardLattice.finMat D.sp.cm.sig V.gram g).mulVec y ∈ Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E ((Formalism.MainNotions.StandardLatticesGL3.stdL D V.rank : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) : Set (Fin V.rank → D.host.E))) → Formalism.MainNotions.StandardLatticesGL3.SuppInert D (GlobalTheory.BotClassDict.finStd V hG g : GL (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) ∧ Formalism.MainNotions.StandardLatticesGL3.IntG D (GlobalTheory.BotClassDict.finStd V hG g : GL (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) :=
  fun V hG _ _ hv _ hg h => ⟨suppInert_finStd V hG hv hg, intG_finStd V hG h⟩

end GlobalTheory.InertLocalPoint
