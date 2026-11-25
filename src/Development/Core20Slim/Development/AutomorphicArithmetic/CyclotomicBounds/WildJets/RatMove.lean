module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
public import Development.Core20Slim.Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ExistsSmallSpherical
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicValuationThetaKernelJetBound
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.HighestWeightBelow
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.VwNatCastNonneg
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.JetKapIff
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkPderivBlockEmbNe
public import Development.AbelianVarietyTheory.Counterexamples.RotationExamples.OneLeAPlLast
public import Formalism.LocalRingCardinality.DataCoeff
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.SatakeDualWeyl.Statement
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Submonoid.BigOperators
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Finsupp.SMul
public import Mathlib.Data.Finsupp.SMulWithZero
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

private theorem lin_rat {ι κ V W : Type} [Fintype ι] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (A : Subfield ℂ) (b : Module.Basis ι ℂ V) (c : Module.Basis κ ℂ W) (f : V →ₗ[ℂ] W)
    (hf : ∀ i j, c.repr (f (b j)) i ∈ A) (v : V) (hv : ∀ j, b.repr v j ∈ A) (i : κ) : c.repr (f v) i ∈ A := by
  rw [← b.sum_repr v]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul]
  exact sum_mem fun j _ => mul_mem (hv j) (hf i j)

private theorem rho_rat {ι E : Type} [Fintype ι] [Field E] {n : ℕ} (A : Subfield ℂ) (emb : ι → E →+* ℂ)
    (hA : ∀ τ x, emb τ x ∈ A) (lam : ι → DomWeight n) (g : GL (Fin n) E) (i j : VVIdx lam) :
    (bVV ℂ lam).repr (rhoVr emb lam g (bVV ℂ lam j)) i ∈ A := by
  refine actionRational_holds ℂ ι n lam A (invTrK (embGL emb g)) (fun τ a b => ?_) i j
  show ((((Formalism.UG.bc (emb τ) g)⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)) b a ∈ A
  rw [← map_inv]
  exact hA τ _

theorem UpperTheory.WildA.ratMove :
    ∀ (D : D7) {n n' : ℕ} (lam : D.what₂.Tau → DomWeight n) (lam' : D.what₂.Tau → DomWeight n') (f f' : VV ℂ lam →ₗ[ℂ] VV ℂ lam')
      (g : GL (Fin n) D.host.E) (g' : GL (Fin n') D.host.E), f' ∘ₗ rhoVr (tauE D) lam g = rhoVr (tauE D) lam' g' ∘ₗ f →
      (∀ i j, (bVV ℂ lam').repr (f (bVV ℂ lam j)) i ∈ Set.range D.what₂.embLL) →
      ∀ i j, (bVV ℂ lam').repr (f' (bVV ℂ lam j)) i ∈ Set.range D.what₂.embLL := by
  intro D n n' lam lam' f f' g g' h hf i j
  have hlab : ∀ τ x, tauE D τ x ∈ D.what₂.embLL.fieldRange := fun τ x =>
    ⟨labLL D τ x, DFunLike.congr_fun (GlobalTheory.ThetaFiresProbe.labE_fixed τ) x⟩
  have e : f' (bVV ℂ lam j) = rhoVr (tauE D) lam' g' (f (rhoVr (tauE D) lam g⁻¹ (bVV ℂ lam j))) := by
    have h1 := LinearMap.congr_fun h (rhoVr (tauE D) lam g⁻¹ (bVV ℂ lam j))
    rw [LinearMap.comp_apply, LinearMap.comp_apply, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
      Module.End.one_apply] at h1
    exact h1
  rw [e]
  exact lin_rat D.what₂.embLL.fieldRange _ _ _ (rho_rat _ _ hlab lam' g') _
    (lin_rat D.what₂.embLL.fieldRange _ _ f hf _ fun k => rho_rat _ _ hlab lam g⁻¹ k j) i
