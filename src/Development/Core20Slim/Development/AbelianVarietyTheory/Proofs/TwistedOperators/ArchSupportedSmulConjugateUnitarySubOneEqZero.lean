module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRtensOp
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.DarbouxModelAlgebraicVectorsLeAdelicSchwartzStatement
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulRealAdEqZero
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
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Pi
public import Mathlib.Algebra.Ring.Prod
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Maps

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.ConjFinArch

variable {D : D7}

def eInf (F : Type) [Field F] [NumberField F] : AF F :=
  ((1 : Ainf F), (0 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F))

theorem one_sub_eInf_fst (F : Type) [Field F] [NumberField F] : (1 - eInf F).1 = 0 := by
  show (1 : Ainf F) - 1 = 0
  exact sub_self _

theorem evI_sub_eInf (F : Type) [Field F] [NumberField F] : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F (1 - eInf F) = 0 := by
  rw [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI, one_sub_eInf_fst, map_zero]

theorem eInf_smul_tmul (a : AF D.host.F) (y : D.host.E) :
    eInf D.host.F • (a ⊗ₜ[D.host.F] y) = (eInf D.host.F * a) ⊗ₜ[D.host.F] y := by
  rfl

def incInf (F : Type) [Field F] [NumberField F] : Ainf F →ₗ[F] AF F where
  toFun x := ((x, (0 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F)) : AF F)
  map_add' x y := by
    show ((x + y, (0 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F)) : Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) = (x + y, 0 + 0)
    rw [add_zero]
  map_smul' c x := by
    show ((c • x, (0 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F)) : Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) = (c • x, c • (0 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F))
    rw [smul_zero]

theorem eInf_mul' (a : AF D.host.F) : eInf D.host.F * a = incInf D.host.F (fstA D.host.F a) := by
  show ((1 : Ainf D.host.F) * a.1, (0 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) * a.2) = (a.1, 0)
  rw [one_mul, zero_mul]

theorem cA_tmul (a : AF D.host.F) (y : D.host.E) :
    cA D (a ⊗ₜ[D.host.F] y) = a ⊗ₜ[D.host.F] D.sp.cm.sig y := by
  show Algebra.TensorProduct.map (AlgHom.id D.host.F (AF D.host.F)) D.sp.cm.sig (a ⊗ₜ[D.host.F] y) = _
  rw [Algebra.TensorProduct.map_tmul]
  rfl

theorem smul_tmul_AF (r a : AF D.host.F) (y : D.host.E) :
    r • (a ⊗ₜ[D.host.F] y) = (r * a) ⊗ₜ[D.host.F] y := rfl

theorem cA_smul (r : AF D.host.F) (x : AF D.host.F ⊗[D.host.F] D.host.E) : cA D (r • x) = r • cA D x := by
  induction x using TensorProduct.induction_on with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | tmul a y => rw [smul_tmul_AF, cA_tmul, cA_tmul, smul_tmul_AF]
  | add x y hx hy => rw [smul_add, map_add (f := _), hx, hy, map_add (f := _), smul_add]

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem eInf_smul (x : AF D.host.F ⊗[D.host.F] D.host.E) :
    eInf D.host.F • x = TensorProduct.map (incInf D.host.F) LinearMap.id
      (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E) x) := by
  have key : DistribSMul.toLinearMap D.host.F (AF D.host.F ⊗[D.host.F] D.host.E) (eInf D.host.F) =
      (TensorProduct.map (incInf D.host.F) (LinearMap.id : D.host.E →ₗ[D.host.F] D.host.E)).comp
        (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E)).toLinearMap := by
    refine TensorProduct.ext' fun a y => ?_
    show eInf D.host.F • (a ⊗ₜ[D.host.F] y) = TensorProduct.map (incInf D.host.F) LinearMap.id
      (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E) (a ⊗ₜ[D.host.F] y))
    rw [eInf_smul_tmul, eInf_mul', Algebra.TensorProduct.map_tmul]
    rfl
  exact LinearMap.congr_fun key x

theorem eInf_smul_eq_zero {x : AF D.host.F ⊗[D.host.F] D.host.E}
    (hx : Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E) x = 0) : eInf D.host.F • x = 0 := by
  rw [eInf_smul, hx, map_zero]

theorem one_apply_map {R S : Type} [Semiring R] [Semiring S] {n : ℕ} (f : R →+* S) (i j : Fin n) :
    f ((1 : Matrix (Fin n) (Fin n) R) i j) = (1 : Matrix (Fin n) (Fin n) S) i j := by
  rw [Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem eInf_smul_conjU_sub_one (V : HSp D) {J : Matrix (Fin V.rank) (Fin V.rank) D.host.E} (c : D.host.E)
    (hJ : J = c • V.gram) {g : GA D V} (hg : g ∈ GfC V) (i j : Fin V.rank) :
    eInf D.host.F • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU V c hJ g) - 1) i j = 0 := by
  have hm : (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU V c hJ g) - 1) i j = cA D (mt V g i j - (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j) := by
    rw [map_sub, Matrix.sub_apply, one_apply_map]
    rfl
  have hinf : infHom V g = 1 := hg
  have he : Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E) (mt V g i j) =
      (1 : Matrix (Fin V.rank) (Fin V.rank) (Ainf D.host.F ⊗[D.host.F] D.host.E)) i j := by
    have := congrArg (fun h : GL (Fin V.rank) (Ainf D.host.F ⊗[D.host.F] D.host.E) => h.1 i j) hinf
    exact this
  rw [hm, ← cA_smul, eInf_smul_eq_zero, map_zero]
  rw [map_sub, he]
  exact sub_eq_zero.2 (one_apply_map (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom i j).symm

end GlobalTheory.ConjFinArch

theorem GlobalTheory.ConjFinArch.smul_mat_conjU_sub_one : ∀ (D : D7) (V : HSp D) {J : Matrix (Fin V.rank) (Fin V.rank) D.host.E} (c : D.host.E) (hJ : J = c • V.gram)
    (g : GA D V), g ∈ GfC V → ∀ u : AF D.host.F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) u →
      u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU V c hJ g) - 1) = 0 := by
  intro D V J c hJ g hg u hu
  have h1 : (1 - GlobalTheory.ConjFinArch.eInf D.host.F) * u = 0 := hu _ (GlobalTheory.ConjFinArch.evI_sub_eInf _)
  have h2 : u = u * GlobalTheory.ConjFinArch.eInf D.host.F := by
    rw [sub_mul, one_mul, sub_eq_zero] at h1
    rw [mul_comm]; exact h1
  rw [h2, mul_smul]
  have h3 : GlobalTheory.ConjFinArch.eInf D.host.F • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU V c hJ g) - 1) = 0 := by
    ext i j
    rw [Matrix.smul_apply, GlobalTheory.ConjFinArch.eInf_smul_conjU_sub_one V c hJ hg i j, Matrix.zero_apply]
  rw [h3, smul_zero]
