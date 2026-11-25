module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairPtsClasses
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairPtsEqSum
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.MovFn
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilActionSchrodingerModelFiniteIdempotent
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsThetaAtOfVac
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevRowSuccInfUA
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.InvVolConjLevelOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ActOChiRight
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.HermitianColumns.InLocalDiscriminantKernel
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.SatakeDualWeyl.Statement
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
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Basic
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.RowVertexInv
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.RowVertexInv

open Matrix

theorem mulVec_conj_mulVec_eq {n : ℕ} {R : Type} [CommRing R] (a g : GL (Fin n) R) (v : Fin n → R) :
    (a : Matrix (Fin n) (Fin n) R) *ᵥ (((a⁻¹ * g * a : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) *ᵥ v) =
      (g : Matrix (Fin n) (Fin n) R) *ᵥ ((a : Matrix (Fin n) (Fin n) R) *ᵥ v) := by
  simp only [Matrix.mulVec_mulVec, Units.val_mul, ← mul_assoc, Units.mul_inv, one_mul]


set_option maxHeartbeats 1000000 in
theorem moved_keeps_std : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T} (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.grid (j + 1) D.R.m)), finG (G.V (.grid (j + 1) D.R.m)) k ∈ S.levRow t (j + 1) hj.le → ∀ v : Fin (G.V (.grid (j + 1) D.R.m)).rank → Formalism.IndefR.Lev.EAf D, (v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat (S.N.fr (.grid (j + 1) D.R.m))) ↔ Matrix.mulVec (Formalism.IndefR.Lev.finE (G.V (.grid (j + 1) D.R.m)) (moved S j k)).1 v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat (S.N.fr (.grid (j + 1) D.R.m)))) := by
  intro D T L sc G W U S t j hj k hk v
  have hD : DefNode D.R.m (.grid (j + 1) D.R.m) := ⟨hj.le, rfl⟩
  have hmax : finG (G.V (.grid (j + 1) D.R.m)) k ∈ G.levMax (.grid (j + 1) D.R.m) := by
    rw [← GlobalTheory.FunObj.GridChoice.levRow_succ_inf_UA W S t j hj.le]
    exact Subgroup.mem_inf.2 ⟨hk, GlobalTheory.LevSplit.finE_mem_UA _ _⟩
  rw [GridData.levMax, congLev_top] at hmax
  have hst := (Subgroup.mem_inf.1 hmax).2
  have e : Formalism.IndefR.Lev.finE (G.V (.grid (j + 1) D.R.m)) (moved S j k) =
      (Formalism.IndefR.Lev.finE (G.V (.grid (j + 1) D.R.m)) (S.N.u (.grid (j + 1) D.R.m)).1)⁻¹ * finG (G.V (.grid (j + 1) D.R.m)) k * Formalism.IndefR.Lev.finE (G.V (.grid (j + 1) D.R.m)) (S.N.u (.grid (j + 1) D.R.m)).1 := by
    rw [moved]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv]
    rfl
  rw [S.N.u_lat _ hD v, S.N.u_lat _ hD, e, mulVec_conj_mulVec_eq]
  exact hst _

end GlobalTheory.RowVertexInv
