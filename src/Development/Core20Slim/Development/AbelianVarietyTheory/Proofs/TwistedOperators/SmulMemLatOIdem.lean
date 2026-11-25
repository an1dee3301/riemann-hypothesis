module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.TensorGiven
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockDetBlockTriangular
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilOver
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaAtSeesawProductDatumEqVacuumCombinations
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.LeastSplitAuxiliaryPrimeThetaChainSpec
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemRangeOfOneTmulMem
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulMemLatO
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridFirstColumnSpaceRankSignatureSelfDual
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Classical
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
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
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Basic
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Trace.Defs
public import Mathlib.Tactic.LinearCombination.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section
namespace GlobalTheory.CosetRow


open Classical in
def extFn {D : D7} {m n : ℕ} (e₀ e₁ : AE D) (Λ : AddSubgroup (Mx D m n)) (Φ : Mx D m n → ℂ) (t : Mx D m n) : ℂ :=
  if IsHalf (e₀ + e₁) t then Φ (e₀ • t) * halfInd e₁ Λ (e₁ • t) else 0

section Gen
variable {D : D7} {m n : ℕ}

theorem symplO_eq_of_half {S T : HSp D} {e₀ e₁ : AE D} (h01 : e₀ * e₁ = 0) (t y : WO S T)
    (ht : IsHalf (e₀ + e₁) t) (hy : IsHalf (cA D e₀) y) : symplO S T t y = symplO S T (e₀ • t) y := by
  have hw : IsHalf e₁ (t - e₀ • t) := fun i j => by
    have := ht i j
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    rw [add_mul] at this
    rw [mul_sub, ← mul_assoc, mul_comm e₁ e₀, h01, zero_mul, sub_zero]
    linear_combination this
  have hz : symplO S T (t - e₀ • t) y = 0 := by
    unfold symplO
    rw [GlobalTheory.VecProd.hO_zero' (a := e₁) (b := e₀) h01 hw hy, mul_zero, map_zero]
  have hs := GlobalTheory.VecProd.symplO_sub t (e₀ • t) y
  rw [hz] at hs
  linear_combination -hs

theorem smul_mem_latO_idem {S T : HSp D} (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E))
    {a : AE D} (ha : a * a = a) {u : WO S T} (hu : u ∈ latO S T LS LT fun _ => True) :
    a • u ∈ latO S T LS LT fun _ => True :=
  GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ a
    (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, ha])) _ hu

end Gen

section Grid
variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}

theorem selfDual_chi {μ₀ : T} (hL : L.Is μ₀) (G : GridData L sc) (i : ℕ) (hi : i < D.R.m) :
    IsSelfDualC (G.pS (.chi i 0)) (G.latS (.chi i 0)) ∧ IsSelfDualC (G.pT (.chi i 0)) (G.latT (.chi i 0)) := by
  have hV : ∀ X : Node, X.InRange D.R.m → (G.V X).SigOK ∧ IsSelfDualC (G.V X) (G.Λ X) := fun X hX => by
    by_cases h0 : ∀ j, X ≠ .grid 0 j
    · exact ⟨(G.isV hX h0).sigOK, (G.isV hX h0).sd⟩
    · push Not at h0
      obtain ⟨j, rfl⟩ := h0
      exact ⟨(GlobalTheory.ChiGrid.colY_isV D T L μ₀ hL j hX.2).sigOK, (GlobalTheory.ChiGrid.colY_isV D T L μ₀ hL j hX.2).sd⟩
  exact ⟨isSelfDualC_neg (hV (.grid (i + 1) 0) ⟨hi, Nat.zero_le _⟩).2, (hV (.grid i 0) ⟨hi.le, Nat.zero_le _⟩).2⟩

end Grid

end GlobalTheory.CosetRow

end
