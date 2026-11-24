module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsGLSubmatrix
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Data.Fin.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RouteSeesaw

variable {D : D7}

def adjM (S B : HSp D) (y : Mx D B.rank S.rank) : Mx D S.rank B.rank :=
  HMul.hMul (HMul.hMul ((S.gram⁻¹).map (incA D) : Matrix (Fin S.rank) (Fin S.rank) (AE D))
    ((y.map (cA D))ᵀ : Matrix (Fin S.rank) (Fin B.rank) (AE D))) (B.gram.map (incA D) : Matrix (Fin B.rank) (Fin B.rank) (AE D))

theorem adjM_zero (S B : HSp D) : adjM S B 0 = 0 := by
  have e : ((0 : Mx D B.rank S.rank).map (cA D)) = 0 := by ext a b; simp
  simp only [adjM, e, transpose_zero, Matrix.mul_zero, Matrix.zero_mul]

theorem adjM_add (S B : HSp D) (y z : Mx D B.rank S.rank) : adjM S B (y + z) = adjM S B y + adjM S B z := by
  have e : (y + z).map (cA D) = y.map (cA D) + z.map (cA D) := by
    ext a b; simp
  simp only [adjM, e, transpose_add, Matrix.mul_add, Matrix.add_mul]

def topR {A B : HSp D} {n : ℕ} (x : Matrix (Fin (A.rank + B.rank)) (Fin n) (AE D)) : Mx D A.rank n :=
  x.submatrix (Fin.castAdd B.rank) id

def botR {A B : HSp D} {n : ℕ} (x : Matrix (Fin (A.rank + B.rank)) (Fin n) (AE D)) : Mx D B.rank n :=
  x.submatrix (Fin.natAdd A.rank) id

def box2 {S A B : HSp D} (φ : WO S A → ℂ) (φ' : WO S B → ℂ) : WO S (GlobalTheory.Doubling.hsum A B) → ℂ :=
  fun x => φ (topR (A := A) (B := B) x) * φ' (botR (A := A) (B := B) x)

theorem externalProductOnHermitianSum_add_left {S A B : HSp D} (φ₁ φ₂ : WO S A → ℂ) (φ' : WO S B → ℂ) :
    box2 (φ₁ + φ₂) φ' = box2 φ₁ φ' + box2 φ₂ φ' := by
  funext x; simp [box2, add_mul]

theorem externalProductOnHermitianSum_smul_left {S A B : HSp D} (c : ℂ) (φ : WO S A → ℂ) (φ' : WO S B → ℂ) :
    box2 (c • φ) φ' = c • box2 φ φ' := by
  funext x; simp [box2, mul_assoc]

end GlobalTheory.RouteSeesaw

end
