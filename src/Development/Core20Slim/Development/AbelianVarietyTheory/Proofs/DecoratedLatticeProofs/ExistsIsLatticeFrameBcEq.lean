module

public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.LatticeFrames.HalfData
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsRealPlacesIdempotentExtensionAdelesStatement
public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
public import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsLatticeFrameIsMajorantFrame
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.SatakeDualWeyl.Statement
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
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Lattice.Full
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.WithAbs
public import Mathlib.Analysis.Normed.Ring.WithAbs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnn

theorem idem_glue_mul {R : Type} [CommRing R] {m : Type} [Fintype m] [DecidableEq m] {e : R} (hee : e * e = e)
    {x y x' y' : Matrix m m R} (h1 : x * x' = 1) (h2 : y * y' = 1) :
    ((1 - e) • x + e • y) * ((1 - e) • x' + e • y') = 1 := by
  have hce : (1 - e) * e = 0 := by rw [sub_mul, one_mul, hee, sub_self]
  have hec : e * (1 - e) = 0 := by rw [mul_sub, mul_one, hee, sub_self]
  have hcc : (1 - e) * (1 - e) = 1 - e := by rw [sub_mul, one_mul, hec, sub_zero]
  simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, h1, h2, hce, hec, hcc, hee, zero_smul,
    add_zero, zero_add]
  rw [← add_smul, sub_add_cancel, one_smul]

def idemGlue {R : Type} [CommRing R] {m : Type} [Fintype m] [DecidableEq m] (e : R) (hee : e * e = e)
    (x y : GL m R) : GL m R :=
  ⟨(1 - e) • (x : Matrix m m R) + e • (y : Matrix m m R),
    (1 - e) • ((x⁻¹ : GL m R) : Matrix m m R) + e • ((y⁻¹ : GL m R) : Matrix m m R),
    idem_glue_mul hee (Units.mul_inv x) (Units.mul_inv y), idem_glue_mul hee (Units.inv_mul x) (Units.inv_mul y)⟩

theorem bc_idemGlue_of_zero {R S : Type} [CommRing R] [CommRing S] {m : Type} [Fintype m] [DecidableEq m] {e : R}
    (hee : e * e = e) (x y : GL m R) (φ : R →+* S) (h : φ e = 0) :
    Formalism.UG.bc φ (idemGlue e hee x y) = Formalism.UG.bc φ x := by
  apply Units.ext
  ext i j
  show φ ((1 - e) * (x : Matrix m m R) i j + e * (y : Matrix m m R) i j) = φ ((x : Matrix m m R) i j)
  rw [map_add (f := _), map_mul, map_mul, map_sub, map_one, h, sub_zero, one_mul, zero_mul, add_zero]

theorem bc_idemGlue_of_one {R S : Type} [CommRing R] [CommRing S] {m : Type} [Fintype m] [DecidableEq m] {e : R}
    (hee : e * e = e) (x y : GL m R) (φ : R →+* S) (h : φ e = 1) :
    Formalism.UG.bc φ (idemGlue e hee x y) = Formalism.UG.bc φ y := by
  apply Units.ext
  ext i j
  show φ ((1 - e) * (x : Matrix m m R) i j + e * (y : Matrix m m R) i j) = φ ((y : Matrix m m R) i j)
  rw [map_add (f := _), map_mul, map_mul, map_sub, map_one, h, sub_self, zero_mul, one_mul, zero_add]

theorem isLatticeFrame_idemGlue {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}
    {L : Submodule (𝓞 E) (Fin n → E)} {e : AF F ⊗[F] E} (hee : e * e = e) {x : GL (Fin n) (AF F ⊗[F] E)}
    (hx : IsLatticeFrame L x) (y : GL (Fin n) (AF F ⊗[F] E)) (he : ∀ v, compFin F E v e = 0) :
    IsLatticeFrame L (idemGlue e hee x y) := by
  intro v z
  rw [bc_idemGlue_of_zero hee x y _ (he v)]
  exact hx v z

theorem exists_isLatticeFrame_bc_eq (D : D7) (A : HSp D) (a : GL (Fin A.rank) (AE D)) :
    ∃ b : GL (Fin A.rank) (AE D), IsLatticeFrame (frameLat A) b ∧
      ∀ w, Formalism.UG.bc (compInf D.host.F D.host.E w) b = Formalism.UG.bc (compInf D.host.F D.host.E w) a := by
  let : Submodule.IsFullLattice D.host.E (frameLat A) := SelfDual.isLattice_frameLat A
  obtain ⟨b₀, hb₀, -⟩ : ∃ b : GL (Fin A.rank) (AE D),
      IsLatticeFrame (frameLat A) b ∧ IsMajorantFrame D.sp.cm.sig A.gram b :=
    Frames.exists_isLatticeFrame_isMajorantFrame (isCMExt_host D) (isHermND_gram A) (frameLat A)
  obtain ⟨e, hee, -, hfin, hinf, -, -⟩ := GlobalTheory.T.exists_realPlacesIdempotent_extensionAdeles D
  exact ⟨idemGlue e hee b₀ a, isLatticeFrame_idemGlue hee hb₀ a hfin, fun w => bc_idemGlue_of_one hee b₀ a _ (hinf w)⟩

end GlobalTheory.StdUnn
