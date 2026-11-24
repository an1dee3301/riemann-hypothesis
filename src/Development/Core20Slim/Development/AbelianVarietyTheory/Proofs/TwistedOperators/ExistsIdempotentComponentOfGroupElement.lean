module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConstMemBddAut
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.CutIsometry
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
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
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
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
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Maps

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.GfCut

variable {R : Type} [CommRing R] {n : ℕ}

theorem idem_mul (φ : R) (hφ : φ * φ = φ) (A B : Matrix (Fin n) (Fin n) R)
    (h : A * B = 1) : (φ • A + (1 - φ) • (1 : Matrix (Fin n) (Fin n) R)) * (φ • B + (1 - φ) • 1) = 1 := by
  have h1 : φ * (1 - φ) = 0 := by rw [mul_sub, mul_one, hφ, sub_self]
  have h2 : (1 - φ) * φ = 0 := by rw [mul_comm, h1]
  have h3 : (1 - φ) * (1 - φ) = 1 - φ := by rw [mul_sub, mul_one, h2, sub_zero]
  simp only [add_mul, mul_add, smul_mul_smul_comm, h, h1, h2, h3, hφ, zero_smul, mul_one, add_zero, zero_add]
  rw [← add_smul, add_sub_cancel, one_smul]

theorem map_idem {T : Type} [CommRing T] (ψ : R →+* T) (f : R) (M : Matrix (Fin n) (Fin n) R) :
    (f • M + (1 - f) • (1 : Matrix (Fin n) (Fin n) R)).map ψ = ψ f • M.map ψ + (1 - ψ f) • 1 := by
  ext i j
  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply, map_add (f := _),
    map_mul, map_sub, map_one]
  split_ifs <;> simp

theorem idem_unitary (σ : R →+* R) (ε : R) (hε : σ ε = ε) (hεε : ε * ε = ε) (J M : Matrix (Fin n) (Fin n) R)
    (h : Formalism.UG.cT σ M * J * M = J) :
    Formalism.UG.cT σ (ε • M + (1 - ε) • (1 : Matrix (Fin n) (Fin n) R)) * J * (ε • M + (1 - ε) • 1) = J :=
  _root_.GlobalTheory.TruncationIsometry.cut_isometry σ ε hε hεε J M h

end GlobalTheory.GfCut

open GlobalTheory.GfCut in
theorem GlobalTheory.GfCut.exists_cut : ∀ {D : D7} (T : HSp D) (g : GA D T) (ε : AE D), g ∈ GfC T → ε * ε = ε → cA D ε = ε → ∃ k : GA D T, k ∈ GfC T ∧ Formalism.L2.Theta.mt T k = ε • Formalism.L2.Theta.mt T g + (1 - ε) • (1 : Matrix (Fin T.rank) (Fin T.rank) (AE D)) := by
  intro D T g ε hg hεε hε
  set M := Formalism.L2.Theta.mt T g with hM
  have hinv : M * ((matHom T g)⁻¹).1 = 1 := (matHom T g).mul_inv
  have hinv' : ((matHom T g)⁻¹).1 * M = 1 := (matHom T g).inv_mul
  let K : GL (Fin T.rank) (AE D) := ⟨ε • M + (1 - ε) • 1, ε • ((matHom T g)⁻¹).1 + (1 - ε) • 1,
    idem_mul ε hεε _ _ hinv, idem_mul ε hεε _ _ hinv'⟩
  have hgU : Formalism.UG.cT (cA D) M * T.gram.map (incA D) * M = T.gram.map (incA D) :=
    (show HR (AF D.host.F) D.sp.cm.sig T.gram from g).2
  have hKU : K ∈ HR (AF D.host.F) D.sp.cm.sig T.gram :=
    idem_unitary (cA D) ε hε hεε _ M hgU
  let k : GA D T := (⟨K, hKU⟩ : HR (AF D.host.F) D.sp.cm.sig T.gram)
  refine ⟨k, ?_, rfl⟩
  have hg1 : infHom T g = 1 := hg
  show infHom T k = 1
  have hg2 := congrArg Units.val hg1
  apply Units.ext
  change (ε • M + (1 - ε) • (1 : Matrix (Fin T.rank) (Fin T.rank) (AE D))).map _ = 1
  rw [map_idem]
  change M.map _ = 1 at hg2
  rw [hg2, ← add_smul, add_sub_cancel, one_smul]

end
