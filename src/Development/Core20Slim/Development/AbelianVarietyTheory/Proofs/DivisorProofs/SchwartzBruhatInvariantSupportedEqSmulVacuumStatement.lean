module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatInvariantSupportedEqSmulVacuum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftPRouteSmall
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoBarZero
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Invertible.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartzBruhat_invariant_supported_eq_smul_vacuum : ∀ {D : D7} {a a' : ℕ} (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig a a')
    (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (hTr : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om') (L₁ : Submodule (𝓞 D.host.E) (Fin a' → D.host.E)) (L₂ : Submodule (𝓞 D.host.E) (Fin (a + a') → D.host.E))
    (θ : 𝓞 D.host.E) (hθ : (θ : D.host.E) + D.sp.cm.sig θ = 1)
    (ι : ((Fin a' × Fin (a + a') → Fv D.host.F Bs.v₁) → ℂ) →ₗ[ℂ] (Matrix (Fin a') (Fin (a + a')) (Fv D.host.F Bs.v₁) → ℂ)) (hι : Γ.M'.IsLinBar Bs.ψ Bs.τ₁ 1 1 ι)
    (φ₀ : (Fin a' × Fin (a + a') → Fv D.host.F Bs.v₁) → ℂ) (h0 : φ₀ ∈ GlobalTheory.WeilM.SB _) (hne : φ₀ ≠ 0)
    (hfix : (∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV {Γ.V' with L := L₁} {Γ.W with L := L₂} Bs.v₁,
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (evFin D.host.F Bs.v₁) (Γ.M'.co.rho Bs.ψ γ) φ₀
            (Bs.ψ (⅟(2 : AF D.host.F) * symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (inclR (F := D.host.F) (AF D.host.F) (θ : D.host.E))
              (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.V'.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.W.J) γ γ) • φ₀)))
    (huniq : ∀ ψ₀ ∈ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv D.host.F Bs.v₁), (∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV {Γ.V' with L := L₁} {Γ.W with L := L₂} Bs.v₁,
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (evFin D.host.F Bs.v₁) (Γ.M'.co.rho Bs.ψ γ) ψ₀
            (Bs.ψ (⅟(2 : AF D.host.F) * symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (inclR (F := D.host.F) (AF D.host.F) (θ : D.host.E))
              (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.V'.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.W.J) γ γ) • ψ₀)) → ∃ c : ℂ, ψ₀ = c • φ₀),
    ∀ g ∈ GlobalTheory.WeilM.SB (Matrix (Fin a') (Fin (a + a')) (Fv D.host.F Bs.v₁)), (∀ s ∈ GlobalTheory.VacShape.Sa Bs Γ L₁ L₂, ∀ Y, g (Y + s) = g Y) →
      (∀ Y ∉ GlobalTheory.VacShape.Bd Bs Γ L₁ L₂, g Y = 0) → ∃ c : ℂ, g = c • ι φ₀ := by
  first | exact @GlobalTheory.VacUniq.sa_bd_uniq | exact GlobalTheory.VacUniq.sa_bd_uniq | (intros; apply GlobalTheory.VacUniq.sa_bd_uniq <;> assumption)
