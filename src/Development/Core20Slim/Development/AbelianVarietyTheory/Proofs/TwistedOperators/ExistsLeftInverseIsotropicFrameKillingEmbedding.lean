module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.T2SpaceHalfAdelicMatrixAddSubgroup
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FinTensMemLatO
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.SatakeDualWeyl.Statement
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Function
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
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Prod
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Ker
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.Order.Notation

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.HalfAverage
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HalfAverage

theorem exists_leftInv_frame_kill_emb : ∀ (D : D7) (V V' : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∃ K : Matrix (Fin r) (Fin V.rank) D.host.E, K * C = 1 ∧ K * B = 0 := by
  intro D V V' r C B hs
  have hadj : ∀ {m n : ℕ} (X : Matrix (Fin m) (Fin n) D.host.E), adj D X = Xᴴ := fun X => rfl
  have hG : V.gramᴴ = V.gram := by
    ext i j; simp [Matrix.conjTranspose_apply, GlobalTheory.LatVac.gram_star]
  have hBC : adj D B * V.gram * C = 0 := by
    have h := congrArg Matrix.conjTranspose hs.orth
    rw [hadj] at h ⊢
    simpa [Matrix.conjTranspose_mul, hG, Matrix.mul_assoc] using h
  let f := C.mulVecLin.coprod B.mulVecLin
  have hf : ∀ c b, f (c, b) = C *ᵥ c + B *ᵥ b := fun c b => rfl
  have hker : LinearMap.ker f = ⊥ := by
    refine LinearMap.ker_eq_bot'.2 fun ⟨c, b⟩ h => ?_
    rw [hf] at h
    have h1 := congrArg ((adj D B * V.gram).mulVec) h
    rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hBC, hs.isom, Matrix.zero_mulVec,
      zero_add, Matrix.mulVec_zero] at h1
    have hb : b = 0 := Matrix.mulVec_injective_iff_isUnit.2
      ((Matrix.isUnit_iff_isUnit_det _).2 (GlobalTheory.LatVac.gram_det_isUnit V')) (by rw [h1, Matrix.mulVec_zero])
    subst hb
    rw [Matrix.mulVec_zero, add_zero] at h
    have hc : c = 0 := Matrix.mulVec_injective_iff.2 hs.frame.2.1 (by rw [h, Matrix.mulVec_zero])
    subst hc
    rfl
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective f hker
  have key : ∀ c b, g (C *ᵥ c + B *ᵥ b) = (c, b) := fun c b => by
    rw [← hf]; exact LinearMap.congr_fun hg (c, b)
  have k1 : ∀ c, g (C *ᵥ c) = (c, 0) := fun c => by simpa using key c 0
  have k2 : ∀ b, g (B *ᵥ b) = (0, b) := fun b => by simpa using key 0 b
  refine ⟨LinearMap.toMatrix' (LinearMap.fst _ _ _ ∘ₗ g), ?_, ?_⟩
  · apply Matrix.toLin'.injective
    refine LinearMap.ext fun v => ?_
    simp [Matrix.toLin'_mul, Matrix.toLin'_apply, k1]
  · apply Matrix.toLin'.injective
    refine LinearMap.ext fun v => ?_
    simp [Matrix.toLin'_mul, Matrix.toLin'_apply, k2]

end GlobalTheory.HalfAverage

end
