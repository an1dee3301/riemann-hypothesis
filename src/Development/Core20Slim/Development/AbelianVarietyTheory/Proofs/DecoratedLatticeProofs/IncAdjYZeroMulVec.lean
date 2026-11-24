module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.LatticeFrames.SmallPair
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSelfDualLatticeAtPlaceLatticeCompletion
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FractionalIdealCompletionLocallyPrincipal
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EventuallyIncAMulMemIntAt
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticeLocalEqIntegralAlmostAll
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilDatumAtPlaceEqLatticeIntertwinerMulDetChar
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SmulColMul
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompProjAnisotropicAnisotropicEmbedding
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittCoreEmbeddingPreservesSupportedUnitarySubgro
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedBessel
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.ByCases
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Fin.Lemmas
public import Init.Data.Int.Basic
public import Init.Data.Int.Lemmas
public import Init.Data.Int.Order
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Pi.Basic
public import Mathlib.Algebra.Opposites
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Ideal.BigOperators
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Matrix ValuativeRel IsLocalRing
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.FinPl GlobalTheory.FinPlLoc GlobalTheory.IwaPlace NumberField Filter
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000

namespace GlobalTheory.GoodPos

variable {D : D7}

theorem incAdj_yZero_mulVec {V₀ W W₀ : HSp D} {ρ : ℕ} (d : HypDec W W₀ ρ) (r : Fin ρ) (hr : r.1 + 1 = ρ)
    (z : Fin V₀.rank → D.host.E) (a : AE D) (y : Fin V₀.rank → AE D) :
    (show Matrix (Fin W.rank) (Fin V₀.rank) (AE D) from d.incAdj V₀ (a • yZero V₀ ρ z)) *ᵥ y =
      colMul d.jY r (incA D D.host.xi0⁻¹ * hermAt V₀ y (a • ratV z)) := by
  have h1 : (incA D (-D.host.xi0⁻¹) • (adj (a • yZero V₀ ρ z) ⬝ gA V₀)) *ᵥ y =
      Pi.single r (incA D D.host.xi0⁻¹ * hermAt V₀ y (a • ratV z)) := by
    rw [smul_mulVec, ← mulVec_mulVec, herm_eq]
    generalize gA V₀ *ᵥ y = t
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, mulVec, dotProduct, adj, yZero, zEll, ell, Matrix.transpose_apply,
      Matrix.map_apply, Matrix.smul_apply, Matrix.neg_apply, vecMulVec_apply, RingHom.map_neg]
    by_cases hi : i = r
    · subst hi
      simp only [hr, if_true, mul_one, Pi.single_eq_same, mul_neg, RingHom.map_neg, neg_mul, Finset.sum_neg_distrib, neg_neg]
    · have : ¬ (i.1 + 1 = ρ) := fun h => hi (Fin.ext (by omega))
      simp only [this, if_false, mul_zero, neg_zero, RingHom.map_zero, zero_mul, Finset.sum_const_zero, Pi.single_eq_of_ne hi]
  change (d.jY ⬝ (incA D (-D.host.xi0⁻¹) • (adj (a • yZero V₀ ρ z) ⬝ gA V₀))) *ᵥ y = _
  rw [← mulVec_mulVec, h1, mulVec_single]
  funext k
  exact mul_comm _ _

theorem mxAt_mul {P : Pl D → Prop} {l m n : ℕ} (M : Mx D l m) {N : Mx D m n} (h : MxAt P N) : MxAt P (M ⬝ N) := fun i j => by
  rw [Matrix.mul_apply]; exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ (h k j)

theorem mxAt_mul' {P : Pl D → Prop} {l m n : ℕ} {M : Mx D l m} (N : Mx D m n) (h : MxAt P M) : MxAt P (M ⬝ N) := fun i j => by
  rw [Matrix.mul_apply]; exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_right _ _ (h i k)

theorem mxAt_smul {P : Pl D → Prop} {m n : ℕ} (a : AE D) {N : Mx D m n} (h : MxAt P N) : MxAt P (a • N) := fun i j =>
  Ideal.mul_mem_left _ _ (h i j)

theorem mxAt_adj {x : Pl D} {m n : ℕ} {N : Mx D m n} (h : MxAt (· = x) N) : MxAt (· = x) (adj N) := fun i j =>
  id_conj (h j i)

def xiU (D : D7) : (AE D)ˣ := inU D.host.xi0 (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D)






section Split

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {p : SplitPt D k}





end Split

end GlobalTheory.GoodPos

end
