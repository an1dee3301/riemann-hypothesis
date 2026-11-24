module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Formalism.LocalToGlobal.ProjectiveLattices.CuspidalL2Subspace
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.InfFam
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
public import Formalism.LocalToGlobal.IndefiniteReal.LinksExistW
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SatakeDualWeyl.Statement
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Opposite
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Opposite
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.GroupWithZero.Units.Lemmas
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Basic
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Opposites
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.Normal.Defs
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.CMField
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open scoped ComplexOrder

namespace GlobalTheory.FockPos

variable {D : D7}

def frAt {n : ℕ} (fr : GL (Fin n) D.host.E) (τ : D.what₂.Tau) : Matrix (Fin n) (Fin n) ℂ :=
  fr.1.map (tauE D τ)

def zCo (θ : InfFam D) {S T : HSp D} (frS : GL (Fin S.rank) D.host.E) (frT : GL (Fin T.rank) D.host.E) (w : WO S T) :
    Formalism.MainNotions.TaylorLogMetric.VC D S.rank T.rank :=
  fun τ => (frAt frT τ)⁻¹ * compAt θ τ w * frAt frS τ

def gaussO (θ : InfFam D) {S T : HSp D} (frS : GL (Fin S.rank) D.host.E) (frT : GL (Fin T.rank) D.host.E) (w : WO S T) : ℂ :=
  Complex.exp (-((Real.pi * Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, ((‖zCo θ frS frT w τ a b‖ ^ 2 : ℝ) : ℂ))

theorem cartan_eq_one {k : ℕ} {G s : Matrix (Fin k) (Fin k) ℂ} (h : IsCartanInv G s) (hG : G.PosDef) : s = 1 := by
  obtain ⟨hss, -, hP⟩ := h
  have key : ∀ v : Fin k → ℂ, (s - 1) *ᵥ v = 0 := by
    intro v
    by_contra hx
    set x := (s - 1) *ᵥ v with hxdef
    have hsx : s *ᵥ x = -x := by
      rw [hxdef, Matrix.mulVec_mulVec, Matrix.mul_sub, hss, Matrix.mul_one, ← neg_sub, Matrix.neg_mulVec]
    have h1 := hP.dotProduct_mulVec_pos hx
    have h2 := hG.dotProduct_mulVec_pos hx
    rw [← Matrix.mulVec_mulVec, hsx, Matrix.mulVec_neg, dotProduct_neg] at h1
    have := add_pos h1 h2
    simp at this
  have : s - 1 = 0 := by
    ext i j
    have := congrFun (key (Pi.single j 1)) i
    simpa [Matrix.mulVec_single] using this
  exact sub_eq_zero.1 this

theorem frAt_det_ne {n : ℕ} (fr : GL (Fin n) D.host.E) (τ : D.what₂.Tau) : (frAt fr τ).det ≠ 0 := by
  have e : (frAt fr τ).det = tauE D τ fr.1.det := (RingHom.map_det (tauE D τ) fr.1).symm
  rw [e, map_ne_zero]
  exact ((Matrix.isUnit_iff_isUnit_det _).1 fr.isUnit).ne_zero

theorem frAt_on {S : HSp D} (fr : GL (Fin S.rank) D.host.E)
    (h : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) fr.1 * S.gram * fr.1 = 1) (τ : D.what₂.Tau) :
    (frAt fr τ)ᴴ * gramAt D S τ * frAt fr τ = 1 := by
  have hs : ∀ x : D.host.E, tauE D τ ((D.sp.cm.sig : D.host.E →+* D.host.E) x) = star (tauE D τ x) := fun x => by
    have := D.host.isCMField_hostE
    exact NumberField.IsCMField.complexEmbedding_complexConj D.host.E _ x
  have h2 := congrArg (fun M => M.map (tauE D τ)) h
  simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] at h2
  rw [← h2, frAt, gramAt]
  congr 2
  ext i j
  simp [Formalism.UG.cT, Matrix.conjTranspose_apply]
  exact (hs _).symm

theorem gramAt_posDef {S : HSp D} (fr : GL (Fin S.rank) D.host.E)
    (h : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) fr.1 * S.gram * fr.1 = 1) (τ : D.what₂.Tau) :
    (gramAt D S τ).PosDef := by
  have hMd : IsUnit (frAt fr τ).det := isUnit_iff_ne_zero.2 (frAt_det_ne fr τ)
  have hM : IsUnit (frAt fr τ) := (Matrix.isUnit_iff_isUnit_det _).2 hMd
  have hMHd : IsUnit (frAt fr τ)ᴴ.det := by rw [Matrix.det_conjTranspose]; exact hMd.star
  have h1 := frAt_on fr h τ
  have e : ((frAt fr τ)⁻¹)ᴴ * 1 * (frAt fr τ)⁻¹ = gramAt D S τ := by
    calc ((frAt fr τ)⁻¹)ᴴ * 1 * (frAt fr τ)⁻¹
        = ((frAt fr τ)ᴴ)⁻¹ * ((frAt fr τ)ᴴ * gramAt D S τ * frAt fr τ) * (frAt fr τ)⁻¹ := by
          rw [h1, Matrix.conjTranspose_nonsing_inv]
      _ = (((frAt fr τ)ᴴ)⁻¹ * (frAt fr τ)ᴴ) * gramAt D S τ * (frAt fr τ * (frAt fr τ)⁻¹) := by
          simp only [Matrix.mul_assoc]
      _ = gramAt D S τ := by
          rw [Matrix.nonsing_inv_mul _ hMHd, Matrix.mul_nonsing_inv _ hMd, Matrix.one_mul, Matrix.mul_one]
  rw [← e]
  refine Matrix.PosDef.one.conjTranspose_mul_mul_same ?_
  exact Matrix.mulVec_injective_of_isUnit (Matrix.isUnit_nonsing_inv_iff.2 hM)

theorem cart_one {S : HSp D} (fr : GL (Fin S.rank) D.host.E)
    (h : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) fr.1 * S.gram * fr.1 = 1)
    {s : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} (hs : ∀ τ, IsCartanInv (gramAt D S τ) (s τ)) : s = fun _ => 1 := by
  funext τ
  have h1 : (gramAt D S τ).PosDef := gramAt_posDef fr h τ
  exact cartan_eq_one (hs τ) h1

end GlobalTheory.FockPos
