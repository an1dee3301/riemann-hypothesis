module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GoodConstOfAniso
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
public import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactUnipFlag
public import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
public import Development.AbelianVarietyTheory.Definitions.Foundations.ConstTermOnMulLeftOfNormalizer
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsUniqueIsProdMeasureFinAway
public import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Formalism.SatakeDualWeyl.Statement
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Nonempty
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Quot
public import Mathlib.Data.Set.Defs
public import Mathlib.GroupTheory.Coset.Defs
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.MeasureTheory.OuterMeasure.AE
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Filter.Basic
public import Mathlib.Topology.Algebra.Group.Subgroup
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Sets.Compacts
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RapidDecay
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal Topology

namespace GlobalTheory.CompanionTheory.RapidDecay

theorem norm_le_of_unipRad_variation : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ φ : GAd σ J → ℂ, (∀ γ ∈ ratPts σ J, ∀ g, φ (γ * g) = φ g) → Continuous φ → IsCuspidal σ J φ → ∀ (k : ℕ) (Cc : Matrix (Fin n) (Fin k) E), 0 < k → GlobalTheory.UAut.IsIsoCols σ J Cc → ∀ (g : GAd σ J) (e : ℝ), (∀ m ∈ unipRad σ J Cc, ‖φ (m * g) - φ g‖ ≤ e) → ‖φ g‖ ≤ e := by
  intro F E _ _ _ _ _ σ hCM n J hJ φ hleft hcont hcusp k Cc hk hC g e he
  haveI := GlobalTheory.UAut.locallyCompact_unipRad hCM hJ hC
  have hc : GlobalTheory.Cusp.Cocompact (ratPts σ J) (unipRad σ J Cc) := GlobalTheory.UAut.cocompact_unipRad hCM hJ hC
  haveI hP := hc.isProbabilityMeasure
  have hL : GlobalTheory.AutomorphicL2Unitary.LeftInv (ratPts σ J) φ := hleft
  have h0 : GlobalTheory.Cusp.constTermOn (ratPts σ J) (unipRad σ J Cc) φ g = 0 :=
    (hc.constTermOn_eq_zero_iff (GlobalTheory.AutomorphicL2Unitary.isFundamentalDomain_stdDom _ Measure.haar) hL g).2
      (hcusp k Cc ⟨hk, hC.1, hC.2⟩ _ _ inferInstance (GlobalTheory.AutomorphicL2Unitary.isFundamentalDomain_stdDom _ _) g)
  have hI := hc.integrable hL hcont g
  have key : φ g = ∫ q, (φ g - φ ((q.out : unipRad σ J Cc) * g))
      ∂GlobalTheory.Cusp.probMeasure (ratPts σ J) (unipRad σ J Cc) := by
    rw [integral_sub (integrable_const _) hI]
    have h0' : ∫ q, φ ((q.out : unipRad σ J Cc) * g)
        ∂GlobalTheory.Cusp.probMeasure (ratPts σ J) (unipRad σ J Cc) = 0 := h0
    rw [h0', integral_const]
    simp
  rw [key]
  have hb := norm_integral_le_of_norm_le_const (μ := GlobalTheory.Cusp.probMeasure (ratPts σ J) (unipRad σ J Cc))
    (f := fun q => φ g - φ ((q.out : unipRad σ J Cc) * g)) (C := e)
    (.of_forall fun q => by rw [norm_sub_rev]; exact he _ (q.out : unipRad σ J Cc).2)
  simpa using hb

end GlobalTheory.CompanionTheory.RapidDecay

end
