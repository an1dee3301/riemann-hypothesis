module

public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.OpGenOf
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocCellSt
public import Batteries.Logic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ModerateGrowthSchwartz
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobData
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.FourierZeroN
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocOpSt
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocalL2IsometryAlt
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.OpGenB
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.OpGenC
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.OpGenSt
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.IsSingTest
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.NullSec
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
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
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.CStarMatrix
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Tactic.FieldSimp.Lemmas
public import Mathlib.Tactic.Group

@[expose] public section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.GenOpsH

theorem gen_nbar (hU : UnipTau) (hW : WEx) (hS : SchOps) (hF : FTfact)
    {D : D7} {n : ℕ} {V : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {χ : (AE D)ˣ →* Circle} {θ : InfFam D}
    {μ : Measure (Mx D V.rank n)} {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)} {H : G D n → ℝ≥0}
    {l : D.what₂.Tau → ℝ} {s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ} {ν : Measure (GA D V)}
    {τ : D.what₂.Tau} {ε : Fin V.rank → Bool} {fr : Matrix (Fin V.rank) (Fin V.rank) ℂ} {ι : GR n →* G D n}
    (hC : Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι) (y : GR n) (c : Matrix (Fin n) (Fin n) ℂ) (hc : cᴴ = c)
    (hyc : mR y = nbar c) :
    ∃ κ γ : ℂ, κ ≠ 0 ∧ ((∃ (Ψ : Mx D V.rank n → ℂ) (x₀ : Mx D V.rank n), AwayCls θ τ fr Ψ ∧ Ψ x₀ ≠ 0) → γ ≠ 0) ∧
      (∀ f : (Fin V.rank → Fin n → ℂ) → ℂ, IsSch f → IsSch (fun u => κ⁻¹ * ftLoc ε (-tLoc l τ) f u) ∧
        IsSch (fun u => κ * ftLoc ε (tLoc l τ) f u)) ∧
      ∀ (Ψ : Mx D V.rank n → ℂ) (hΨ : AwayCls θ τ fr Ψ) (f : (Fin V.rank → Fin n → ℂ) → ℂ) (hf : IsSch f),
        (ω (ι y) ⟨tens θ τ fr f Ψ, hΨ.2 f hf⟩).1 = tens θ τ fr (fun u => γ⁻¹ * (κ * ftLoc ε (tLoc l τ)
          (fun v => Complex.exp (Complex.I * (tLoc l τ : ℂ) * ((-c) * gramX ε v).trace) *
            (κ⁻¹ * ftLoc ε (-tLoc l τ) f v)) u)) Ψ := by
  have hfr : IsUnit fr.det := hC.hfr.1
  obtain ⟨w, hw⟩ := hW D n
  obtain ⟨yn, hyn⟩ := OG.exists_nU n (-c) (by rw [Matrix.conjTranspose_neg, hc])
  have hιn : ι yn = w⁻¹ * ι y * w := OG.iota_conj hC.hθ hC.hι w hw y yn c hyc hyn
  have hιy : ι y = w * ι yn * w⁻¹ := by rw [hιn]; group
  obtain ⟨κ, A, A', hκ, hFT⟩ := hF D n V ψ χ θ μ ω H l s ν τ ε fr ι hC w hw
  obtain ⟨f0, hf0, hf00⟩ := (hS V.rank n).2.2.2.2
  have h0 := hFT 0 (OG.awayCls_zero τ fr)
  let e : (Fin V.rank → Fin n → ℂ) → ℂ := fun u =>
    Complex.exp (Complex.I * (tLoc l τ : ℂ) * ((-c) * gramX ε u).trace)
  let F' : ((Fin V.rank → Fin n → ℂ) → ℂ) → (Fin V.rank → Fin n → ℂ) → ℂ := fun f u =>
    κ⁻¹ * ftLoc ε (-tLoc l τ) f u
  let Fw : ((Fin V.rank → Fin n → ℂ) → ℂ) → (Fin V.rank → Fin n → ℂ) → ℂ := fun f u => κ * ftLoc ε (tLoc l τ) f u
  have hc' : (-c)ᴴ = -c := by rw [Matrix.conjTranspose_neg, hc]
  have hE : ∀ f, IsSch f → IsSch (fun u => e u * F' f u) := fun f hf =>
    (hS V.rank n).2.2.2.1 ε (tLoc l τ) (-c) (F' f) hc' ((h0.2.2 f hf).2.1)
  set γ : ℂ := Fw (F' f0) (0 : Matrix (Fin V.rank) (Fin n) ℂ) with hγdef

  have hrelAll : ∀ Ψ (hΨ : AwayCls θ τ fr Ψ), ∀ x, Ψ x = γ * A (A' Ψ) x := by
    intro Ψ hΨ
    obtain ⟨hAΨ, hA'Ψ, hFΨ⟩ := hFT Ψ hΨ
    have kA := hFT (A' Ψ) hA'Ψ
    have hcons : ∀ g (hg : IsSch g), tens θ τ fr g Ψ = tens θ τ fr (Fw (F' g)) (A (A' Ψ)) := by
      intro g hg
      have k1g := (hFΨ g hg).2.2.2
      have kcg := (kA.2.2 (F' g) ((hFΨ g hg).2.1)).2.2.1
      have hΦ1 : ω w⁻¹ ⟨tens θ τ fr g Ψ, hΨ.2 g hg⟩ = ⟨tens θ τ fr (F' g) (A' Ψ), hA'Ψ.2 _ ((hFΨ g hg).2.1)⟩ :=
        Subtype.ext k1g
      have hid : ω w (ω w⁻¹ ⟨tens θ τ fr g Ψ, hΨ.2 g hg⟩) = ⟨tens θ τ fr g Ψ, hΨ.2 g hg⟩ := by
        rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
      rw [hΦ1] at hid
      rw [← kcg, hid]
    intro x
    obtain ⟨x', hx'1, hx'2, hx'3⟩ := OG.exists_slice hC.hθ τ x (fr * (0 : Matrix (Fin V.rank) (Fin n) ℂ))
    have h1 := congrFun (hcons f0 hf0) x'
    have hf00' : f0 (0 : Matrix (Fin V.rank) (Fin n) ℂ) = 1 := hf00
    rw [OG.tens_at τ hfr _ _ x' 0 hx'1, OG.tens_at τ hfr _ _ x' 0 hx'1, hf00', one_mul, hΨ.1 x' x hx'2 hx'3,
      kA.1.1 x' x hx'2 hx'3] at h1
    exact h1
  refine ⟨κ, γ, hκ, ?_, fun f hf => ⟨(h0.2.2 f hf).2.1, (h0.2.2 f hf).1⟩, ?_⟩
  · rintro ⟨Ψ, x₀, hΨ, hx₀⟩ hγ
    exact hx₀ (by rw [hrelAll Ψ hΨ x₀, hγ, zero_mul])
  intro Ψ hΨ f hf
  obtain ⟨hAΨ, hA'Ψ, hFΨ⟩ := hFT Ψ hΨ
  have k1 := (hFΨ f hf).2.2.2
  have kA := hFT (A' Ψ) hA'Ψ
  have kr := (kA.2.2 (fun u => e u * F' f u) (hE f hf)).2.2.1
  have hrel := hrelAll Ψ hΨ
  by_cases hγ : γ = 0
  · have hΨ0 : Ψ = 0 := funext fun x => by rw [hrel x, hγ, zero_mul]; rfl
    subst hΨ0
    have hz : (⟨tens θ τ fr f 0, hΨ.2 f hf⟩ : schwartzA θ V.rank n) = 0 := Subtype.ext (by funext x; simp [tens])
    rw [hz, map_zero]
    funext x
    simp [tens]
  · have hstep : ω (ι y) ⟨tens θ τ fr f Ψ, hΨ.2 f hf⟩ =
        ω w ⟨tens θ τ fr (fun u => e u * F' f u) (A' Ψ), hA'Ψ.2 _ (hE f hf)⟩ := by
      rw [hιy, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply]
      congr 1
      apply Subtype.ext
      funext x
      rw [hU D n V ψ χ θ μ ω H l s ν τ ε fr ι hC yn (-c) hc' hyn, k1]
      simp only [tens, e, F', mul_assoc]
    funext x
    rw [hstep, kr]
    simp only [tens]
    rw [hrel x]
    simp only [e, F']
    field_simp

end PositivityTheory.Rg.Sw.Glob.GenOpsH
