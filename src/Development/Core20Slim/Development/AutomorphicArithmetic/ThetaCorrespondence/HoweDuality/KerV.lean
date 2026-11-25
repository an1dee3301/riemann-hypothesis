module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicArithmetic.ThetaCorrespondence.HoweDuality.FactorApply
public import Development.Core20Slim.Development.WeilBound.ThetaLifts.SphericalLattices.ThetaSubSup
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelInfAlt
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatchedMapsGaussianTransform
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatchedMapsOrbitKernel
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaSubGAlgDOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HypothesesAbsDet
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationLocalAtFinitePlaceUnitaryGroupStatement
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExists
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Ker
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Module.Submodule.LinearMap
public import Mathlib.Algebra.Module.Submodule.Map
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Set.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.BoundedOrder.Basic
public import Mathlib.Order.CompleteLattice.Defs
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open UpperTheory.Lit.HoweDuality GlobalTheory.HoweGlobalPair

theorem UpperTheory.Lit.HoweDuality.kerV :
    ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {Bs : Base F E} {a a' : ℕ} {G : Geo σ a a'} {Xc : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W} {R : RealMaps F a a'} {Rf : FinMaps F a a'}, IsMatched Bs G Xc om om' R Rf → ∀ v : Pl (F := F), relFin om v ≤ LinearMap.ker (Rf.p v ∘ₗ (SB (Fin a × Fin (a + a') → Fv F v)).subtype) ∧ Stable (opFin om v) (LinearMap.ker (Rf.p v ∘ₗ (SB (Fin a × Fin (a + a') → Fv F v)).subtype)) ∧ LinearMap.ker (Rf.p v ∘ₗ (SB (Fin a × Fin (a + a') → Fv F v)).subtype) ≠ ⊤ ∧ ∀ N : Submodule ℂ ↥(SB (Fin a × Fin (a + a') → Fv F v)), LinearMap.ker (Rf.p v ∘ₗ (SB (Fin a × Fin (a + a') → Fv F v)).subtype) ≤ N → Stable (opFin om v) N → N ≠ ⊤ → N ≤ LinearMap.ker (Rf.p v ∘ₗ (SB (Fin a × Fin (a + a') → Fv F v)).subtype) := by
  intro F E _ _ _ _ _ σ Bs a a' G Xc om om' R Rf hM v
  have hT := hM.triple
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx
    exact hM.fin.inv v hx
  · rintro g ⟨h, hh, hg⟩ x hx
    have hx' : Rf.p v (x : (Fin a × Fin (a + a') → Fv F v) → ℂ) = 0 := hx
    have h0 : Acts (evFin F v) (om' (1, h)) (0 : (Fin a' × Fin (a + a') → Fv F v) → ℂ) 0 := by
      intro r _
      have ht : tens (evFin F v) (0 : (Fin a' × Fin (a + a') → Fv F v) → ℂ) r = 0 := by
        funext y; simp [tens]
      rw [ht, map_zero]
    have e := hM.fin.equiv v h hh x x.2 0 (zero_mem _) (g x) (g x).2 0 (zero_mem _) (hg x) h0
      (by rw [hx', map_zero])
    show Rf.p v ((g x : SB _) : (Fin a × Fin (a + a') → Fv F v) → ℂ) = 0
    rw [e, map_zero]
  · intro hKe
    have hbot : (SB (Fin a × Fin (a + a') → Fv F v)).map (Rf.p v) = ⊥ := by
      rw [Submodule.eq_bot_iff]
      rintro _ ⟨ψ, hψ, rfl⟩
      have hm : (⟨ψ, hψ⟩ : SB (Fin a × Fin (a + a') → Fv F v)) ∈
          LinearMap.ker (Rf.p v ∘ₗ (SB (Fin a × Fin (a + a') → Fv F v)).subtype) := by
        rw [hKe]; exact Submodule.mem_top
      exact hm
    rw [hM.fin.onto v] at hbot
    haveI := hM.fin.nontriv v
    exact top_ne_bot hbot
  · intro N hKN hst hne
    have key : ∀ x : SB (Fin a × Fin (a + a') → Fv F v),
        Rf.p v x ∈ (N.map (SB (Fin a × Fin (a + a') → Fv F v)).subtype).map (Rf.p v) → x ∈ N := by
      rintro x ⟨_, ⟨n, hn, rfl⟩, hpn⟩
      have hk : x - n ∈ N := hKN (by
        rw [LinearMap.mem_ker, map_sub, sub_eq_zero]
        exact hpn.symm)
      have := N.add_mem hn hk
      rwa [add_sub_cancel] at this
    rcases hM.fin.irred v ((N.map (SB (Fin a × Fin (a + a') → Fv F v)).subtype).map (Rf.p v)) (by
      intro h hh ψ hψ ψ₁ hψ₁ hact hpm
      have hx : (⟨ψ, hψ⟩ : SB (Fin a × Fin (a + a') → Fv F v)) ∈ N := key ⟨ψ, hψ⟩ hpm
      have e := GlobalTheory.ThK.LocalOps.acts_unique v _ hψ hact (GlobalTheory.HoweGlobal.FinPlace.locOp_acts hT v hh ⟨ψ, hψ⟩)
      exact Submodule.mem_map_of_mem ⟨GlobalTheory.HoweGlobal.FinPlace.locOp hT v hh ⟨ψ, hψ⟩,
        hst _ (GlobalTheory.HoweGlobal.FinPlace.locOp_mem hT v hh) _ hx, e.symm⟩) with h0 | htop
    · intro x hx
      have hmem : Rf.p v x ∈ (N.map (SB (Fin a × Fin (a + a') → Fv F v)).subtype).map (Rf.p v) :=
        Submodule.mem_map_of_mem ⟨x, hx, rfl⟩
      rw [h0] at hmem
      exact (Submodule.mem_bot ℂ).1 hmem
    · exfalso
      apply hne
      rw [Submodule.eq_top_iff']
      intro x
      apply key
      rw [htop]; exact Submodule.mem_top
