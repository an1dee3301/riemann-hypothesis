module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryUnimodularExistsFundamentalDomain
public import Development.AbelianVarietyTheory.Definitions.Foundations.MemSiegelOfIffRightAct
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HermitianOrthogonalExtensionData
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.SatakeDualWeyl.Statement
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Countable.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Dynamics.Ergodic.Action.Basic
public import Mathlib.Dynamics.Ergodic.Action.Regular
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Logic.Function.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Group.Arithmetic
public import Mathlib.MeasureTheory.Group.Defs
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.Group.MeasurableEquiv
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.MeasurableSpace.Embedding
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Order
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SquareComm

variable {D : D7} {M X V : HSp D} (ω : WRep M X) (j : GA D V → GA D X) (G : GA D V → ℂ)
  (ν : Measure (GA D M)) (𝓕 : Set (GA D M)) (μ : Measure (GA D V)) (𝓔 : Set (GA D V))

variable {ω j G ν 𝓕 μ 𝓔}

theorem ofSgn_symm_mem_GQ (ε : Bool) {γ : GA D M} (hγ : γ ∈ GQ M) : (ofSgn ε M).symm γ ∈ GQ (sgn ε M) := by
  have hγ' : γ.1 ∈ HFin (AF D.host.F) D.sp.cm.sig M.gram := hγ
  cases ε
  · exact hγ'
  · have hm : γ.1 ∈ HFin (AF D.host.F) D.sp.cm.sig (-M.gram) := by
      unfold HFin at hγ' ⊢
      rw [UJ_neg]
      exact hγ'
    rw [← neg_gram] at hm
    exact hm

theorem integral_rightTranslate (h : IsHaarFD M ν 𝓕) {f : GA D M → ℂ} (hf : ∀ γ ∈ GQ M, ∀ w, f (γ * w) = f w) (u : GA D M) :
    (IntegrableOn (fun w => f (w * u)) 𝓕 ν ↔ IntegrableOn f 𝓕 ν) ∧ ∫ w in 𝓕, f (w * u) ∂ν = ∫ w in 𝓕, f w ∂ν := by
  obtain ⟨hH, hFD⟩ := h
  obtain ⟨_, _, _, hB, hTG, _, hC⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D M
  have : ν.IsMulRightInvariant :=
    (GlobalTheory.Mem.AdelicGroupFund.rightInvariant_and_exists_fundamentalDomain D M ν hH).1
  have hpres : MeasurePreserving (fun w => w * u) ν ν := measurePreserving_mul_right ν u
  have hemb : MeasurableEmbedding (fun w : GA D M => w * u) := (MeasurableEquiv.mulRight u).measurableEmbedding
  set S : Set (GA D M) := (fun w => w * u⁻¹) ⁻¹' 𝓕 with hSdef
  have hS : IsFundamentalDomain (GQ M) S ν :=
    hFD.preimage_of_equiv (measurePreserving_mul_right ν u⁻¹).quasiMeasurePreserving Function.bijective_id
      (fun g x => by simp only [id, Subgroup.smul_def, smul_eq_mul, mul_assoc])
  have hset : (fun w => w * u) ⁻¹' S = 𝓕 := by
    ext w
    simp [hSdef]
  have hinv : ∀ (g : GQ M) (x : GA D M), f (g • x) = f x := fun g x => hf g g.2 x
  refine ⟨?_, ?_⟩
  · have h1 := hpres.integrableOn_comp_preimage hemb (f := f) (s := S)
    rw [hset] at h1
    exact h1.trans (hS.integrableOn_iff hFD hinv)
  · have h2 := hpres.setIntegral_preimage_emb hemb f S
    rw [hset] at h2
    exact h2.trans (hS.setIntegral_eq hFD hinv)

end GlobalTheory.SquareComm

end
