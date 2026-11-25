module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.PureTensorLIntertwine
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationCommFockPolynomialVectors
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BiThetaOfVac
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OmPureTensorOOfFinite
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulEqZeroOfInf
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Sets
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FockComb

theorem om_pureTensorO_comb : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : Om S T), IsInfFam θ → IsWeilDatumO ψ S T χS χT om → ∀ sS sT BS BT (e : WO S T →₀ ℂ) (f₀ f : WO S T → ℂ) (x : ℂ), IsFinComb e → IsThetaFunO ψ S T f₀ → IsThetaFunO ψ S T f → ∀ b ∈ GfC S, ∀ b' ∈ GfC T, om (b, b') f = x • comb ψ S T e f₀ → ∀ P, ∀ a ∈ GinfC S, ∀ a' ∈ GinfC T, om (a * b, a' * b') (pureTensorO ψ θ S T sS sT BS BT f P) = x • comb ψ S T e (om (a, a') (pureTensorO ψ θ S T sS sT BS BT f₀ P)) ∧ ∀ (N : Lat S) (N' : Lat T), Vac ψ S T N N' (fun _ => True) f₀ → Vac ψ S T N N' (fun _ => True) (om (a, a') (pureTensorO ψ θ S T sS sT BS BT f₀ P)) := by
  intro D ψ θ S T χS χT om hθ hW sS sT BS BT e f₀ f x he hf₀ hf b hb b' hb' hfx P a ha a' ha'
  have hψ : IsStdChar D ψ (-1) := hW.std

  have hfin := GlobalTheory.OrientedHeis.om_pureTensorO D ψ θ S T χS χT om hW hθ sS sS BS BS sT sT BT BT b b'
    (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ hb, Matrix.mul_one, Matrix.one_mul])
    (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ hb', Matrix.mul_one, Matrix.one_mul])
    (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ hb, Matrix.one_mul])
    (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ hb', Matrix.one_mul]) f hf P
  have hth₀ : IsThetaFunO ψ S T (pureTensorO ψ θ S T sS sT BS BT f₀ P) :=
    (GlobalTheory.OrientedHeis.om_pureTensorO D ψ θ S T χS χT om hW hθ sS sS BS BS sT sT BT BT 1 1
      (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ (one_mem _), Matrix.mul_one, Matrix.one_mul])
      (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ (one_mem _), Matrix.mul_one, Matrix.one_mul])
      (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ (one_mem _), Matrix.one_mul])
      (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ (one_mem _), Matrix.one_mul]) f₀ hf₀ P).1

  have hcomb : comb ψ S T e (pureTensorO ψ θ S T sS sT BS BT f₀ P) =
      pureTensorO ψ θ S T sS sT BS BT (comb ψ S T e f₀) P := by
    let q := e.support.equivFin
    have key := (GlobalTheory.FockFiniteHeis.heis_comb_pureTensorO D ψ θ S T hψ hθ sS sT BS BT f₀ hf₀ e.support.card
      (fun i => e (q.symm i).1) (fun i => (q.symm i).1) (fun i => he _ (q.symm i).2) P).1
    have h1 : ∀ g : WO S T → (WO S T → ℂ), ∑ u ∈ e.support, e u • g u = ∑ i, e (q.symm i).1 • g (q.symm i).1 := by
      intro g
      rw [← Finset.sum_coe_sort e.support]
      exact (Equiv.sum_comp q.symm (fun u : e.support => e u.1 • g u.1)).symm
    simp only [comb]
    rw [h1, h1]
    exact key
  refine ⟨?_, fun N N' hv => ?_⟩
  · have e1 : ((a * b, a' * b') : GA D S × GA D T) = (a, a') * (b, b') := rfl
    rw [e1, map_mul, Module.End.mul_apply, hfin.2, hfx, GlobalTheory.FiniteFock.pureTensorO_smul, ← hcomb, map_smul,
      GlobalTheory.FrComb.om_comb hW ha ha' he hth₀]
  · refine ⟨hW.om_pres _ _ hth₀, GlobalTheory.FrComb.latVac_om hW ha ha' hth₀ ?_⟩
    have fix : ∀ u ∈ latO S T (N : Set _) (N' : Set _) (fun _ => True), heisO ψ S T u f₀ = f₀ →
        heisO ψ S T u (pureTensorO ψ θ S T sS sT BS BT f₀ P) = pureTensorO ψ θ S T sS sT BS BT f₀ P := by
      intro u hu h0
      have := ((GlobalTheory.FinTranslate.finite_translate D ψ θ S T hψ hθ f₀ hf₀).2 u (GlobalTheory.SplitScalar.latO_fin hu)).2 sS BS sT BT P
      rw [← this, h0]
    exact ⟨fun u hu => fix (2 • u) (AddSubgroup.nsmul_mem _ hu 2) (hv.2.1 u hu),
      fun e' he' u hu hh => fix u hu (hv.2.2 e' he' u hu hh)⟩

end GlobalTheory.FockComb
