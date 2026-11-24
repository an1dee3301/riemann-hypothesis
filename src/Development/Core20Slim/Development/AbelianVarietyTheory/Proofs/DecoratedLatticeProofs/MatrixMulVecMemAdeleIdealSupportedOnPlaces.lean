module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LineLatAt
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.BaseMatrixGlApply
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompProjAnisotropicAnisotropicEmbedding
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
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.PropLemmas
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Ideal.BigOperators
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Pointwise

noncomputable section

namespace GlobalTheory.FinPl

theorem matrix_mulVec_mem_adeleIdealSupportedOnPlaces {D : D7} {P : Pl D → Prop} {m n : ℕ} (A : Matrix (Fin m) (Fin n) (AE D))
    (y : Fin n → AE D) (hy : ∀ i, y i ∈ idAt D P) (i : Fin m) : (A *ᵥ y) i ∈ idAt D P := by
  simp only [Matrix.mulVec, dotProduct]
  exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hy j)

theorem matrixColumnScaledByAdele_zero {D : D7} {m n : ℕ} (x : Mx D m n) (i : Fin n) : colMul x i 0 = 0 := by
  funext k; simp [colMul]

theorem carriesLattice_wittEmbedding_iff_core : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (L : GlobalTheory.FinPl.Lat S) (L₀ : GlobalTheory.FinPl.Lat S₀) (v : GlobalTheory.FinPl.Pl D) (g : GA D S₀), GlobalTheory.FinPl.MonoAt d L L₀ v → (GlobalTheory.FinPl.Moves S (d.emb0 g) L L (· = v) ↔ GlobalTheory.FinPl.Moves S₀ g L₀ L₀ (· = v)) := by
  intro D S S₀ ρ d L L₀ v g hM
  have hpX : ∀ z : Fin S₀.rank → AE D, d.pX *ᵥ (d.j0 *ᵥ z) = 0 := fun z => by
    rw [Matrix.mulVec_mulVec, d.pX_j0, Matrix.zero_mulVec]
  have hpY : ∀ z : Fin S₀.rank → AE D, d.pY *ᵥ (d.j0 *ᵥ z) = 0 := fun z => by
    rw [Matrix.mulVec_mulVec, d.pY_j0, Matrix.zero_mulVec]
  have hp0 : ∀ z : Fin S₀.rank → AE D, d.p0 *ᵥ (d.j0 *ᵥ z) = z := fun z => by
    rw [Matrix.mulVec_mulVec, d.p0_j0, Matrix.one_mulVec]
  have key : ∀ z : Fin S₀.rank → AE D, d.j0 *ᵥ z ∈ latV S L (· = v) ↔ z ∈ latV S₀ L₀ (· = v) := fun z => by
    rw [hM, hpX, hpY, hp0]
    simp only [Pi.zero_apply, matrixColumnScaledByAdele_zero, zero_mem, implies_true, true_and]
  have hj : ∀ z : Fin S₀.rank → AE D, mt S (d.emb0 g) *ᵥ (d.j0 *ᵥ z) = d.j0 *ᵥ (mt S₀ g *ᵥ z) := fun z => by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, d.wittDecomp_anisotropicEmbedding_inclAnisotropic]
  constructor
  · intro h z hz
    rw [← key, ← key, ← hj]
    exact h _ (matrix_mulVec_mem_adeleIdealSupportedOnPlaces _ _ hz)
  · intro h y hy
    have eX : d.pX *ᵥ (mt S (d.emb0 g) *ᵥ y) = d.pX *ᵥ y := by rw [Matrix.mulVec_mulVec, d.wittDecomp_projX_anisotropicEmbedding]
    have eY : d.pY *ᵥ (mt S (d.emb0 g) *ᵥ y) = d.pY *ᵥ y := by rw [Matrix.mulVec_mulVec, d.wittDecomp_projY_anisotropicEmbedding]
    have e0 : d.p0 *ᵥ (mt S (d.emb0 g) *ᵥ y) = mt S₀ g *ᵥ (d.p0 *ᵥ y) := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, d.wittDecomp_projAnisotropic_anisotropicEmbedding]
    rw [hM y, hM (mt S (d.emb0 g) *ᵥ y), eX, eY, e0]
    exact and_congr Iff.rfl (and_congr Iff.rfl (h _ (matrix_mulVec_mem_adeleIdealSupportedOnPlaces _ _ hy)))

end GlobalTheory.FinPl

end
