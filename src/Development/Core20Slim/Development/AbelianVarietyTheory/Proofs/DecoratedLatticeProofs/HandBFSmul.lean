module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsBiSmooth
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompProjAnisotropicAnisotropicEmbedding
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

namespace I195MixedCoordinates_234e4f75c563de28cf3cb155

open Formalism.BasicNotions Formalism.BasicNotions.TH
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.MixModel MeasureTheory
attribute [local instance] Formalism.BasicNotions.Host.cmStar

public noncomputable abbrev source
    {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (T : HSp D)
    (ψ : AddChar (AF D.host.F) ℂ) (μ : Measure (Mx D T.rank ρ))
    (𝓕 : Set (Mx D T.rank ρ)) (f : WO S T → ℂ) (x : Mx D T.rank ρ) : WO S₀ T → ℂ :=
  fun w₀ => ∫ a in 𝓕, heisO ψ S T (a * d.pY)
    (heisO ψ S T (x * d.pX) (heisO ψ S T (w₀ * d.p0) f)) 0 ∂μ

public noncomputable abbrev target
    {D : D7} {T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ) (S : HSp D)
    (ψ : AddChar (AF D.host.F) ℂ) (μ : Measure (Mx D ρ S.rank))
    (𝓕 : Set (Mx D ρ S.rank)) (f : WO S T → ℂ) (y : Mx D S.rank ρ) : WO S T₀ → ℂ :=
  fun w₀ => ∫ ξ in 𝓕, heisO ψ S T (d.jX * ξ)
    (heisO ψ S T (d.jY * (incA D (-D.host.xi0⁻¹) • (adj y * gA S)))
      (heisO ψ S T (d.j0 * w₀) f)) 0 ∂μ

end I195MixedCoordinates_234e4f75c563de28cf3cb155

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HandHom
variable {D : D7}

theorem mixS_smul {V V₀ : HSp D} {ρ : ℕ} (d : HypDec V V₀ ρ) (T : HSp D) (ψ : AddChar (AF D.host.F) ℂ)
    (μ : Measure (Mx D T.rank ρ)) (𝓕 : Set (Mx D T.rank ρ)) (a : ℂ) (f : WO V T → ℂ) (x : Mx D T.rank ρ) :
    (_root_.I195MixedCoordinates_234e4f75c563de28cf3cb155.source d) T ψ μ 𝓕 (a • f) x = a • (_root_.I195MixedCoordinates_234e4f75c563de28cf3cb155.source d) T ψ μ 𝓕 f x := by
  funext w₀
  simp only [_root_.I195MixedCoordinates_234e4f75c563de28cf3cb155.source, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]
  congr 1; funext a'; simp only [heisO, Pi.smul_apply, smul_eq_mul]; ring

theorem mixT_smul {W W₀ : HSp D} {ρ : ℕ} (d : HypDec W W₀ ρ) (S : HSp D) (ψ : AddChar (AF D.host.F) ℂ)
    (μ : Measure (Mx D ρ S.rank)) (𝓕 : Set (Mx D ρ S.rank)) (a : ℂ) (f : WO S W → ℂ) (y : Mx D S.rank ρ) :
    (_root_.I195MixedCoordinates_234e4f75c563de28cf3cb155.target d) S ψ μ 𝓕 (a • f) y = a • (_root_.I195MixedCoordinates_234e4f75c563de28cf3cb155.target d) S ψ μ 𝓕 f y := by
  funext w₀
  simp only [_root_.I195MixedCoordinates_234e4f75c563de28cf3cb155.target, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]
  congr 1; funext a'; simp only [heisO, Pi.smul_apply, smul_eq_mul]; ring

theorem flatAt_smul (ψ : AddChar (AF D.host.F) ℂ) {V V₀ W W₀ : HSp D} {ρ σ : ℕ} (dV : HypDec V V₀ ρ)
    (dW : HypDec W W₀ σ) (μS : Measure (Mx D W.rank ρ)) (𝓕S : Set (Mx D W.rank ρ)) (μT : Measure (Mx D σ V₀.rank))
    (𝓕T : Set (Mx D σ V₀.rank)) (νU : Measure (UX D ρ)) (x : Mx D W.rank ρ) (y : Mx D V₀.rank σ) (a : ℂ)
    (Ψ : WO V W → ℂ) :
    GlobalTheory.MixPer.flatAt ψ dV dW μS 𝓕S μT 𝓕T νU x y (a • Ψ) = a • GlobalTheory.MixPer.flatAt ψ dV dW μS 𝓕S μT 𝓕T νU x y Ψ := by
  have hS (f : WO V W → ℂ) (z : Mx D W.rank ρ) :
      _root_.I195MixedCoordinates_14b5fd3aa93c7f4842f1a892.source dV W ψ μS 𝓕S (a • f) z =
        a • _root_.I195MixedCoordinates_14b5fd3aa93c7f4842f1a892.source dV W ψ μS 𝓕S f z :=
    mixS_smul dV W ψ μS 𝓕S a f z
  have hT (f : WO V₀ W → ℂ) (z : Mx D V₀.rank σ) :
      _root_.I195MixedCoordinates_14b5fd3aa93c7f4842f1a892.target dW V₀ ψ μT 𝓕T (a • f) z =
        a • _root_.I195MixedCoordinates_14b5fd3aa93c7f4842f1a892.target dW V₀ ψ μT 𝓕T f z :=
    mixT_smul dW V₀ ψ μT 𝓕T a f z
  funext w
  simp only [GlobalTheory.MixPer.flatAt, GlobalTheory.MixPer.flatFun, GlobalTheory.MixPer.evalAt, hS, Pi.smul_apply,
    smul_eq_mul]
  rw [← integral_const_mul]
  congr 1; funext u; rw [hT]; simp only [Pi.smul_apply, smul_eq_mul]; ring

end GlobalTheory.HandHom

namespace GlobalTheory.HandHom
variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

theorem flatBF_smul {ρ : ℕ} {B : BesLev D ρ} {J : JacLev D ρ} (s : StepBF ψ B J) (a : ℂ) (Ψ : WO B.V J.W → ℂ) :
    flatBF s (a • Ψ) = a • flatBF s Ψ := by
  simp only [GlobalTheory.Unf.flatBF, GlobalTheory.MixPer.flat, flatAt_smul]

theorem flatFB_smul {σ : ℕ} {J : JacLev D (σ + 1)} {B : BesLev D σ} (s : StepFB ψ J B) (a : ℂ) (Ψ : WO J.W B.V → ℂ) :
    flatFB s (a • Ψ) = a • flatFB s Ψ := by
  simp only [GlobalTheory.Unf.flatFB, GlobalTheory.MixPer.flatLast, flatAt_smul]





end GlobalTheory.HandHom

namespace GlobalTheory.HandHom
variable {D : D7}


end GlobalTheory.HandHom
