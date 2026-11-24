module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsLatticeFrameIsMajorantFrame
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAHEqOfMemRatPts
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatIffOfSelfDual
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalVolumeLift
public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
public import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
public import Development.AbelianVarietyTheory.Definitions.Foundations.MemSiegelOfIffRightAct
public import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SatakeDualWeyl.Statement
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Opposite
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Opposite
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Lattice.Full
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Pi.Basic
public import Mathlib.Algebra.Opposites
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.Core.Rk.AInt

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem det_mem_intLoc_of_mapsTo {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) [Submodule.IsFullLattice E L]
    (v : HeightOneSpectrum (𝓞 F)) (X : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E))
    (hX : ∀ x ∈ latLoc F L v, X *ᵥ x ∈ latLoc F L v) : X.det ∈ intLoc F E v := by
  obtain ⟨a, ha⟩ := Frames.exists_isLatticeFrame (F := F) L
  set b := Formalism.UG.bc (compFin F E v) a with hb
  set N : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) := (b⁻¹).1 * X * b.1 with hN
  have hent : ∀ i j, N i j ∈ intLoc F E v := by
    intro i j
    have h1 : b.1 *ᵥ (Pi.single j 1 : Fin n → Fv F v ⊗[F] E) ∈ latLoc F L v :=
      (ha v (Pi.single j 1)).1 fun l => by
        by_cases e : l = j
        · subst e; simp
        · simp [e]
    have h2 := hX _ h1
    have hbN : b.1 * N = X * b.1 := by
      rw [hN, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]
    have h3 : b.1 *ᵥ (N *ᵥ Pi.single j 1) ∈ latLoc F L v := by
      rwa [Matrix.mulVec_mulVec, hbN, ← Matrix.mulVec_mulVec]
    have h4 := (ha v _).2 h3 i
    simpa using h4
  have hdet : N.det = X.det := by
    rw [hN, Matrix.det_mul, Matrix.det_mul, mul_comm ((b⁻¹).1.det * X.det), ← mul_assoc, ← Matrix.det_mul,
      ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one, one_mul]
  let N' : Matrix (Fin n) (Fin n) (intLoc F E v) := fun i j => ⟨N i j, hent i j⟩
  have hmap : N'.map (intLoc F E v).subtype = N := by ext i j; rfl
  have hd := RingHom.map_det (intLoc F E v).subtype N'
  rw [← hdet, ← hmap, ← RingHom.mapMatrix_apply, ← hd]
  exact (N'.det).2

theorem aH_mem_intLoc_of_lattice (σ : E →ₐ[F] E) {n : ℕ} (Q : Matrix (Fin (n + n)) (Fin (n + n)) E)
    (L : Submodule (𝓞 E) (Fin n → E)) [Submodule.IsFullLattice E L] (v : HeightOneSpectrum (𝓞 F))
    (p : siegelH (Fv F v) σ Q) (hp : (p : GLoc σ Q v) ∈ GlobalTheory.Doubling.KFin σ Q L v) :
    ((aH _ σ Q p : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) ∈ intLoc F E v := by
  have hk : KeepsDiag finSumFinEquiv (GlobalTheory.AdelicU.matHom (Fv F v) σ Q p).1 :=
    (mem_siegelOf (e := finSumFinEquiv) (mat := GlobalTheory.AdelicU.matHom (Fv F v) σ Q)).1 p.2
  refine det_mem_intLoc_of_mapsTo L v (leviMat finSumFinEquiv (GlobalTheory.AdelicU.matHom (Fv F v) σ Q p).1) fun x hx => ?_
  have h1 : pairVec finSumFinEquiv x x ∈ latLoc F (sumLat finSumFinEquiv L L) v := by
    rw [latLoc_sumLat]; exact (pairVec_mem_sumLat _).2 ⟨hx, hx⟩
  have h2 := (mem_stabLoc.1 hp _).1 h1
  rw [hk.mulVec_diag, latLoc_sumLat, pairVec_mem_sumLat] at h2
  exact h2.1

theorem aH_mem_intLoc : ∀ (D : D7) (A : HSp D) (L : Lat A), IsSelfDualC A L → ∀ (v : FinPl D) (p : siegelH (Fv D.host.F v) D.sp.cm.sig (dblSp A).gram), (p : Gv (dblSp A) v) ∈ KFin D.sp.cm.sig (dblSp A).gram L v → ((aH _ D.sp.cm.sig (dblSp A).gram p : (Fv D.host.F v ⊗[D.host.F] D.host.E)ˣ) : Fv D.host.F v ⊗[D.host.F] D.host.E) ∈ intLoc D.host.F D.host.E v := by
  intro D A L hL v p hp
  haveI := GlobalTheory.AdIsom.selfDual_isFullLattice hL
  exact aH_mem_intLoc_of_lattice D.sp.cm.sig (n := A.rank) (dblSp A).gram L v p hp

end GlobalTheory.Core.Rk.AInt
