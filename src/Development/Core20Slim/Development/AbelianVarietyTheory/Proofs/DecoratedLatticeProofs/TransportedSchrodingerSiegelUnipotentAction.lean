module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.LatticeFrames.HalfData
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StandardUnitaryChartUnipotentEqWittUnipotentStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchrodingerFunctionUnitaryLeviRadicalActionsStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchrodingerThetaEqSchwartzBruhatStatement
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ModerateGrowthSchwartz
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalZero
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.LatticeFrames.HeckeFormNSOfHeckeForm
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
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
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Hom.Basic
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.UnitBall
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Trace.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnn.Unip

theorem trace_algebraMap_mul_gen {R S : Type} [CommRing R] [CommRing S] [Algebra R S] (a : R) (t : S) :
    Algebra.trace R S (algebraMap R S a * t) = a * Algebra.trace R S t := by
  rw [← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul]

theorem trace_mul_smul_gen {R : Type} [CommRing R] {n : ℕ} (s : R) (T b : Matrix (Fin n) (Fin n) R) :
    Matrix.trace (T * (s • b)) = s * Matrix.trace (b * T) := by
  rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, Matrix.trace_mul_comm]

theorem incA_xiZero_mul_inv_eq_algebraMap_neg (D : D7) (μ : D.host.E) (lam : D.host.F)
    (hlam : algebraMap D.host.F D.host.E lam = -D.host.xi0 / μ) :
    incA D D.host.xi0 * incA D μ⁻¹ =
      algebraMap (AF D.host.F) (AE D) (-algebraMap D.host.F (AF D.host.F) lam) := by
  have hxm : D.host.xi0 * μ⁻¹ = -algebraMap D.host.F D.host.E lam := by
    rw [hlam, neg_div, neg_neg, div_eq_mul_inv]
  have hinc : incA D (algebraMap D.host.F D.host.E lam) =
      algebraMap (AF D.host.F) (AE D) (algebraMap D.host.F (AF D.host.F) lam) := by
    show (Algebra.TensorProduct.includeRight : D.host.E →ₐ[D.host.F] AF D.host.F ⊗[D.host.F] D.host.E)
      (algebraMap D.host.F D.host.E lam) = _
    rw [AlgHom.commutes, IsScalarTower.algebraMap_apply D.host.F (AF D.host.F) (AF D.host.F ⊗[D.host.F] D.host.E)]
  rw [← map_mul, hxm, map_neg, hinc, map_neg]

theorem neg_trHalf_eq (D : D7) (μ : D.host.E) (lam : D.host.F)
    (hlam : algebraMap D.host.F D.host.E lam = -D.host.xi0 / μ) (t : AE D) :
    -(trHalf D (incA D μ⁻¹ * t)) = algebraMap D.host.F (AF D.host.F) lam * halfTr t := by
  have h1 : Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * (incA D μ⁻¹ * t)) =
      -algebraMap D.host.F (AF D.host.F) lam * Algebra.trace (AF D.host.F) (AE D) t :=
    (congrArg (Algebra.trace (AF D.host.F) (AE D)) ((mul_assoc _ _ t).symm.trans
      (congrArg (· * t) (incA_xiZero_mul_inv_eq_algebraMap_neg D μ lam hlam)))).trans (trace_algebraMap_mul_gen _ t)
  have h2 : ∀ h a z : AF D.host.F, -(h * (-a * z)) = a * (h * z) := fun h a z => by ring
  exact (congrArg (fun y => -(algebraMap D.host.F (AF D.host.F) (1 / 2) * y)) h1).trans (h2 _ _ _)

theorem chr_eq_shift (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (μ : D.host.E) (lam : D.host.F)
    (hlam : algebraMap D.host.F D.host.E lam = -D.host.xi0 / μ) {n : ℕ} (T b : Mx D n n) (c : skewA D n)
    (hc : c.1 = incA D μ⁻¹ • b) :
    chr ψ T c = shift ψ lam (halfTr (Matrix.trace (b ⬝ T : Mx D n n))) := by
  have h1 : Matrix.trace (T ⬝ c.1 : Mx D n n) = incA D μ⁻¹ * Matrix.trace (b ⬝ T : Mx D n n) :=
    (congrArg (fun y : Mx D n n => Matrix.trace (T ⬝ y : Mx D n n)) hc).trans (trace_mul_smul_gen _ T b)
  exact congrArg ψ ((congrArg (fun y => -(trHalf D y)) h1).trans (neg_trHalf_eq D μ lam hlam _))

theorem transport_unip : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χB : (AE D)ˣ →* Circle) (omh : GA D (dblSp A) × GA D B →* Module.End ℂ (WO (dblSp A) B → ℂ)), IsWeilDatumO ψ (dblSp A) B 1 χB omh → ∀ (ν : Measure (WO A B)) (𝓨 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓨 → ∀ θ : InfFam D, IsInfFam θ → ∀ μ : D.host.E, IsSkew μ → ∀ κ : GA D (dblSp A) ≃* G D A.rank, IsChart A μ κ → ∀ omS : G D A.rank →* Module.End ℂ (schwartzA θ B.rank A.rank), IsTransport ψ θ A B ν 𝓨 omh κ omS → ∀ lam : D.host.F, algebraMap D.host.F D.host.E lam = -D.host.xi0 / μ → ∀ (g : G D A.rank) (b : Mx D A.rank A.rank), mat g = blk4 1 b 0 1 → ∀ Φ x, (omS g Φ).1 x = shift ψ lam (halfTr (Matrix.trace (b ⬝ GlobalTheory.StdUnn.inner B x x : Mx D A.rank A.rank))) * Φ.1 x := by
  intro D ψ A B χB omh hW ν 𝓨 hν θ hθ μ hμ κ hκ omS hT lam hlam g b hg Φ x
  obtain ⟨c, hc, hgc⟩ := GlobalTheory.T.standardUnitaryChart_unipotent_eq_wittUnipotent D A μ hμ κ hκ (κ.symm g) b (by rw [MulEquiv.apply_symm_apply]; exact hg)
  obtain ⟨f, hf, hfΦ⟩ := ((GlobalTheory.T.schrodingerTheta_eq_schwartzBruhat D) ψ hW.std θ hθ A B ν 𝓨 hν).2.1 Φ.1 Φ.2
  have h1 := hT (κ.symm g) f hf Φ hfΦ.symm
  rw [MulEquiv.apply_symm_apply] at h1
  rw [h1, hgc, ((GlobalTheory.T.schrodingerFunction_unitary_levi_radical_actions D ψ A B χB omh hW ν 𝓨 hν f hf).2.2.1 c x), hfΦ]
  exact congrArg (· * Φ.1 x) (chr_eq_shift D ψ μ lam hlam _ b c hc)

end GlobalTheory.StdUnn.Unip
