module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubledBasisSkewColumnMatrixGramInverse
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.LatticeFrames.HalfData
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompProjAnisotropicAnisotropicEmbedding
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixSDblDecZero
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SatakeDualWeyl.Statement
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Init.SizeOf
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnn.ChartExist

open Formalism.UG

variable {R : Type} [CommRing R]

theorem cT_mul_gen (σ : R →+* R) {m p q : Type} [Fintype p] (M : Matrix m p R) (N : Matrix p q R) :
    cT σ (M * N) = cT σ N * cT σ M := by
  simp only [cT, Matrix.map_mul, Matrix.transpose_mul]

theorem cT_one_gen (σ : R →+* R) {n : Type} [Fintype n] [DecidableEq n] : cT σ (1 : Matrix n n R) = 1 := by
  simp [cT]

variable {n : Type} [Fintype n] [DecidableEq n]

theorem conj_mem (σ : R →+* R) (Q J : Matrix n n R) (T : GL n R) (c : Rˣ)
    (hT : cT σ (T : Matrix n n R) * Q * T = (c : R) • J) (g : GL n R) (hg : g ∈ UJ σ Q) :
    T⁻¹ * g * T ∈ UJ σ J := by
  have hg' : cT σ (g : Matrix n n R) * Q * g = Q := hg
  show cT σ (((T⁻¹ * g * T : GL n R)) : Matrix n n R) * J * ((T⁻¹ * g * T : GL n R) : Matrix n n R) = J
  have h1 : ((T⁻¹ : GL n R) : Matrix n n R) * T = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have h2 : (T : Matrix n n R) * ((T⁻¹ : GL n R) : Matrix n n R) = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have h3 : cT σ ((T⁻¹ : GL n R) : Matrix n n R) * cT σ (T : Matrix n n R) = 1 := by
    rw [← cT_mul_gen, h2, cT_one_gen]
  have hJ : J = ((c⁻¹ : Rˣ) : R) • (cT σ (T : Matrix n n R) * Q * T) := by
    rw [hT, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]
  rw [hJ]
  simp only [Units.val_mul, cT_mul_gen, Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  calc _ = cT σ (T : Matrix n n R) * cT σ (g : Matrix n n R) *
        (cT σ ((T⁻¹ : GL n R) : Matrix n n R) * cT σ (T : Matrix n n R)) * Q *
        ((T : Matrix n n R) * ((T⁻¹ : GL n R) : Matrix n n R)) * g * T := by
          simp only [Matrix.mul_assoc]
    _ = cT σ (T : Matrix n n R) * (cT σ (g : Matrix n n R) * Q * g) * T := by
          rw [h3, h2]; simp only [Matrix.mul_one, Matrix.mul_assoc]
    _ = cT σ (T : Matrix n n R) * Q * T := by rw [hg']

theorem conj_back (σ : R →+* R) (Q J : Matrix n n R) (T : GL n R) (c : Rˣ)
    (hT : cT σ (T : Matrix n n R) * Q * T = (c : R) • J) :
    cT σ ((T⁻¹ : GL n R) : Matrix n n R) * J * ((T⁻¹ : GL n R) : Matrix n n R) = ((c⁻¹ : Rˣ) : R) • Q := by
  have h2 : (T : Matrix n n R) * ((T⁻¹ : GL n R) : Matrix n n R) = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have h3 : cT σ ((T⁻¹ : GL n R) : Matrix n n R) * cT σ (T : Matrix n n R) = 1 := by
    rw [← cT_mul_gen, h2, cT_one_gen]
  have hJ : J = ((c⁻¹ : Rˣ) : R) • (cT σ (T : Matrix n n R) * Q * T) := by
    rw [hT, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]
  rw [hJ, Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  calc cT σ ((T⁻¹ : GL n R) : Matrix n n R) * (cT σ (T : Matrix n n R) * Q * T) * ((T⁻¹ : GL n R) : Matrix n n R)
      = (cT σ ((T⁻¹ : GL n R) : Matrix n n R) * cT σ (T : Matrix n n R)) * Q *
        ((T : Matrix n n R) * ((T⁻¹ : GL n R) : Matrix n n R)) := by simp only [Matrix.mul_assoc]
    _ = Q := by rw [h3, h2, Matrix.one_mul, Matrix.mul_one]

def conjEquiv (σ : R →+* R) (Q J : Matrix n n R) (T : GL n R) (c : Rˣ)
    (hT : cT σ (T : Matrix n n R) * Q * T = (c : R) • J) : UJ σ Q ≃* UJ σ J where
  toFun g := ⟨T⁻¹ * g.1 * T, conj_mem σ Q J T c hT g.1 g.2⟩
  invFun h := ⟨T * h.1 * T⁻¹, by
    have := conj_mem σ J Q T⁻¹ c⁻¹ (conj_back σ Q J T c hT) h.1 h.2
    rwa [inv_inv] at this⟩
  left_inv g := by ext1; simp [mul_assoc]
  right_inv h := by ext1; simp [mul_assoc]
  map_mul' g h := by ext1; simp [mul_assoc]

end GlobalTheory.StdUnn.ChartExist


open GlobalTheory.StdUnn.ChartExist in
theorem GlobalTheory.StdUnn.ChartExist.gram_adelic (D : D7) (A : HSp D) (μ : D.host.E)
    (hgram : (Tm A μ)ᴴ * (dblSp A).gram * Tm A μ = μ • Jst D A.rank)
    (T : GL (Fin (A.rank + A.rank)) (AE D)) (hTv : T.val = rat (Tm A μ)) (c : (AE D)ˣ) (hc : (c : AE D) = incA D μ) :
    Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF D.host.F) D.sp.cm.sig) T.val
      * (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (AF D.host.F) (dblSp A).gram : Matrix (Fin (A.rank + A.rank)) (Fin (A.rank + A.rank)) (AE D)) * T.val
      = (c : AE D) • Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (AF D.host.F) (Jst D A.rank) := by
  have e1 : Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF D.host.F) D.sp.cm.sig) T.val = ((Tm A μ)ᴴ).map (incA D) := by
    rw [hTv]; ext i j; rfl
  rw [e1, hTv, hc]
  change ((Tm A μ)ᴴ).map (incA D) * ((dblSp A).gram).map (incA D) * (Tm A μ).map (incA D) = (incA D μ) • (Jst D A.rank).map (incA D)
  rw [← Matrix.map_mul, ← Matrix.map_mul, hgram]
  ext i j
  simp [Matrix.map_apply, map_mul]


open GlobalTheory.StdUnn.ChartExist in
theorem GlobalTheory.StdUnn.chart_exists : ∀ (D : D7) (A : HSp D) (μ : D.host.E), IsSkew μ → ∃ κ : GA D (dblSp A) ≃* G D A.rank, IsChart A μ κ := by
  intro D A μ hμ
  obtain ⟨hgram, hdet, -⟩ := GlobalTheory.StdUnn.Tm_gram_inv D A μ hμ
  have hdetR : IsUnit (rat (Tm A μ) : Mx D (A.rank + A.rank) (A.rank + A.rank)).det := by
    have : (rat (Tm A μ) : Mx D (A.rank + A.rank) (A.rank + A.rank)).det = incA D (Tm A μ).det := by
      rw [RingHom.map_det]; rfl
    rw [this]; exact hdet.map (incA D)
  let T : GL (Fin (A.rank + A.rank)) (AE D) := Matrix.nonsingInvUnit _ hdetR
  have hTv : T.val = rat (Tm A μ) := rfl
  have hμu : IsUnit (incA D μ) := (Ne.isUnit hμ.1).map (incA D)
  refine ⟨conjEquiv (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF D.host.F) D.sp.cm.sig) _ _ T hμu.unit
    (gram_adelic D A μ hgram T hTv hμu.unit hμu.unit_spec), ?_⟩
  intro g
  show (rat (Tm A μ) : Mx D (A.rank + A.rank) (A.rank + A.rank)) * (T⁻¹ * g.1 * T).val = g.1.val * rat (Tm A μ)
  rw [← hTv]
  simp only [Units.val_mul, ← Matrix.mul_assoc]
  rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]
