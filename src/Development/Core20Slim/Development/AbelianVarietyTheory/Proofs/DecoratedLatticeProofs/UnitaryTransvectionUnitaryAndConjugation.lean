module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.EichlerTransvectionUnitaryInverseConj
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompProjAnisotropicAnisotropicEmbedding
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRationalComplementIsotropicSandwich
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Opposite
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Invertible.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Opposite
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Basic
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Opposites
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Matrix
open GlobalTheory.MixModel GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TransvAdelic

variable {D : D7}

theorem form_mulVec (S : HSp D) {k l : ℕ} (M : Mx D S.rank k) (N : Mx D S.rank l) (x : Fin k → AE D)
    (y : Fin l → AE D) :
    form S (M *ᵥ x) (N *ᵥ y) = (fun i => cA D (y i)) ⬝ᵥ ((adj N ⬝ (gA S ⬝ M)) *ᵥ x) := by
  have h : (fun i => cA D ((N *ᵥ y) i)) = (N.map (cA D)) *ᵥ fun i => cA D (y i) := by
    funext i
    exact RingHom.map_mulVec (cA D) N y i
  rw [form, h, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, dotProduct_mulVec _ (adj N), adj,
    Matrix.vecMul_transpose]

theorem form_act (S : HSp D) (g : GA D S) (x y : VA S) : form S (act S g x) (act S g y) = form S x y := by
  rw [act, act, form_mulVec, mt_unitary, form]

theorem unitary_of_form (S : HSp D) (M : Mx D S.rank S.rank)
    (h : ∀ x y, form S (M *ᵥ x) (M *ᵥ y) = form S x y) : adj M * (gA S * M) = gA S := by
  ext i j
  have := h (Pi.single j 1) (Pi.single i 1)
  have e : (fun k => cA D ((Pi.single i 1 : VA S) k)) = Pi.single i 1 := by
    funext k
    by_cases hk : k = i
    · subst hk; simp
    · simp [hk]
  rw [form_mulVec, form, e] at this
  simpa using this

theorem form_vecX {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (a : Fin ρ → AE D) :
    form S (vecX d a) (vecX d a) = 0 := by
  rw [vecX, form_mulVec, d.gram_XX, Matrix.zero_mulVec, dotProduct_zero]

@[reducible] def starRingA (D : D7) : StarRing (AE D) where
  star := cA D
  star_involutive := cA_cA
  star_mul x y := by rw [map_mul, mul_comm]
  star_add := map_add (cA D)

@[reducible] def invTwo (D : D7) : Invertible (2 : AE D) where
  invOf := half D
  invOf_mul_self := by rw [mul_two, half_add_half]
  mul_invOf_self := by rw [two_mul, half_add_half]

theorem form_transv (S : HSp D) (w v : VA S) (hw : form S w w = 0) (hv : form S w v = 0) (x y : VA S) :
    form S (transv S w v x) (transv S w v y) = form S x y := by
  letI := starRingA D
  letI := invTwo D
  exact (GlobalTheory.eichlerTransvection_unitary_inverse_conj (AE D) (Fin S.rank) (gA S) (adj_gA S) (form S)
    (fun _ _ => rfl) (transv S) (fun _ _ _ => rfl)).1 w v hw hv x y

def transvLin (S : HSp D) (w v : VA S) : VA S →ₗ[AE D] VA S where
  toFun := transv S w v
  map_add' x y := by
    funext i
    simp only [transv, form, Matrix.mulVec_add, dotProduct_add, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  map_smul' s x := by
    funext i
    simp only [transv, form, Matrix.mulVec_smul, dotProduct_smul, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul, RingHom.id_apply]
    ring

theorem toMatrix_transvLin (S : HSp D) (w v y : VA S) :
    LinearMap.toMatrix' (transvLin S w v) *ᵥ y = transv S w v y := by
  rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
  rfl

theorem act_transv (S : HSp D) (g : GA D S) (w v y : VA S) :
    act S g (transv S w v y) = transv S (act S g w) (act S g v) (act S g y) := by
  rw [transv, transv, form_act, form_act, form_act]
  simp only [act, Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_smul]

theorem act_mul (S : HSp D) (g h : GA D S) (y : VA S) : act S (g * h) y = act S g (act S h y) := by
  rw [act, act, act, mt_mul, Matrix.mulVec_mulVec]

theorem transv_unitary_conj :
    ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.TransvUnitary D ∧ GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.TransvConj D := by
  intro D
  refine ⟨fun S S₀ ρ d a v hv => ?_, fun S S₀ ρ d a v _ u g hu y => ?_⟩
  · refine ⟨ofMat S (LinearMap.toMatrix' (transvLin S (vecX d a) v)) (unitary_of_form S _ fun x y => ?_), fun y => ?_⟩
    · rw [toMatrix_transvLin, toMatrix_transvLin, form_transv S _ _ (form_vecX d a) hv]
    · rw [act, mt_ofMat, toMatrix_transvLin]
  · rw [act_mul, act_mul, hu, act_transv, ← act_mul S g g⁻¹, mul_inv_cancel]
    congr 1
    rw [act, mt_one, Matrix.one_mulVec]

end GlobalTheory.TransvAdelic

end
