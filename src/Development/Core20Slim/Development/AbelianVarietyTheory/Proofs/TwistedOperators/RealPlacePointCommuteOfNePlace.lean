module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.KTypeExtension
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemKFinOfMemLowT
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSmoothCuspFormFrechetModerateGrowthRepStatement
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.AtPlaceIffEqAtTau
public import Formalism.FormalDegreeBessel.StatementG
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedSmooth
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Classical
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.ExistsUnique
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

open Classical Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PointAtPlaceComm

open GlobalTheory.PointAtPlace GlobalTheory.PointAtPlaceHom Formalism.MainNotions.StandardLattice

theorem atTau_comm : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (τ τ' : D.what₂.Tau), τ ≠ τ' → ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ g' ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ'), atTau θ V τ g * atTau θ V τ' g' = atTau θ V τ' g' * atTau θ V τ g := by
  intro D θ hθ V τ τ' hne g hg g' hg'
  have ha := atTau_spec hθ V τ hg
  have hb := atTau_spec hθ V τ' hg'
  set a := atTau θ V τ g
  set b := atTau θ V τ' g'
  have k : ∀ (φ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) (x : GA D V),
      infMat D.sp.cm.sig V.gram φ x * infMat D.sp.cm.sig V.gram φ x⁻¹ = 1 := fun φ x => by
    rw [← infMat_mul, mul_inv_cancel, infMat_one]
  have triv : ∀ (φ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) (x : GA D V),
      infMat D.sp.cm.sig V.gram φ x = 1 → infMat D.sp.cm.sig V.gram φ x⁻¹ = 1 := fun φ x h => by
    have := k φ x
    rwa [h, Matrix.one_mul] at this
  have hc : IsAtTau θ V τ 1 (a * b * a⁻¹ * b⁻¹) := by
    have all : ∀ ρ, infMat D.sp.cm.sig V.gram (θ ρ) (a * b * a⁻¹ * b⁻¹) = 1 := fun ρ => by
      simp only [infMat_mul]
      by_cases c : ρ = τ
      · subst c
        have hB : infMat D.sp.cm.sig V.gram (θ ρ) b = 1 := hb.2.2 ρ hne
        rw [hB, triv _ _ hB, Matrix.mul_one, Matrix.mul_one, k]
      · have hA : infMat D.sp.cm.sig V.gram (θ ρ) a = 1 := ha.2.2 ρ c
        rw [hA, triv _ _ hA, Matrix.one_mul, Matrix.mul_one, k]
    exact ⟨mul_mem (mul_mem (mul_mem ha.1 hb.1) (inv_mem ha.1)) (inv_mem hb.1), all τ, fun ρ _ => all ρ⟩
  have h1 : IsAtTau θ V τ 1 (1 : GA D V) := ⟨one_mem _, infMat_one V _, fun _ _ => infMat_one V _⟩
  have e : a * b * a⁻¹ * b⁻¹ = 1 :=
    (existsUnique_isAtTau V τ θ hθ 1 (one_mem_UH _)).unique hc h1
  have e2 : a * b * a⁻¹ = b := mul_inv_eq_one.1 e
  exact mul_inv_eq_iff_eq_mul.1 e2

end GlobalTheory.PointAtPlaceComm

end
