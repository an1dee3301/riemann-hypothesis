module

public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.IntegralUnitCoefficients.CompFinSigR
public import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GenFinLocE
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GenFinSt
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocRedField
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.SatakeDualWeyl.Statement
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Maximal
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

noncomputable section

open scoped Matrix TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta GlobalTheory.AdelicU GlobalTheory.StdUnn IsDedekindDomain NumberField

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.GenFinLocHf

open PositivityTheory.Rg.Sw.Glob.GenFinLocAH

theorem locFE (hF : LocRedField) (hS : LocRedSplit) {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) (hfix : ∀ x, σ x = x ↔ x ∈ (algebraMap F E).range) (v : HeightOneSpectrum (𝓞 F)) {n : ℕ}
    (M M' : Matrix (Fin (n + n)) (Fin (n + n)) (Fv F v ⊗[F] E)) (hM : ∀ i j, M i j ∈ intLoc F E v) (hM' : ∀ i j, M' i j ∈ intLoc F E v)
    (hMM : M * M' = 1) (hU : Formalism.UG.cT (sigR (Fv F v) σ) M * J2 (Fv F v ⊗[F] E) n * M = J2 (Fv F v ⊗[F] E) n) :
    ∃ (a : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) (I : Finset (Fin n)), (∀ i j, a i j ∈ intLoc F E v) ∧
      (a.det ∈ intLoc F E v ∧ ∃ z' ∈ intLoc F E v, a.det * z' = 1) ∧
      ((blkDm (M * GlobalTheory.StdUnn.blk4 a 0 0 ((a.map (sigR (Fv F v) σ)).transpose)⁻¹ * wIm I)).det ∈ intLoc F E v ∧
        ∃ z' ∈ intLoc F E v, (blkDm (M * GlobalTheory.StdUnn.blk4 a 0 0 ((a.map (sigR (Fv F v) σ)).transpose)⁻¹ * wIm I)).det * z' = 1) := by
  obtain ⟨𝔪, h𝔪, horb⟩ := orbit σ hσ hfix v
  exact locSub hF hS (intLoc F E v) (sigR (Fv F v) σ) (sigI σ v) (sigI_sigI σ hσ v) (fun x => sigI_coe _ v x) 𝔪 h𝔪 horb M M' hM hM'
    hMM hU

theorem hmul {D : D7} {n : ℕ} (k : G D n) (v : GlobalTheory.FinPl.Pl D) :
    (mat k).map (GlobalTheory.FinPl.compAt D v) * (mat k⁻¹).map (GlobalTheory.FinPl.compAt D v) = 1 := by
  rw [← Matrix.map_mul]
  show (mat (k * k⁻¹)).map _ = 1
  rw [mul_inv_cancel]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem locFin_of (hF : LocRedField) (hS : LocRedSplit) : LocFin := by
  intro D n k hk v
  have h := locFE hF hS D.sp.cm.sig sig_sig sig_fix v _ _ (int_of_K k hk v) (int_of_K k⁻¹ (inv_mem hk) v) (hmul k v) (uni_comp k v)
  simp only [LocGood, IsIntUnit, cTv]
  with_reducible_and_instances exact h

end PositivityTheory.Rg.Sw.Glob.GenFinLocHf
