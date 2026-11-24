module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.LatticeFrames.HalfData
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompactAdele
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCMFamHost
public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
public import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.EqOrConjOfPlaceOf
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsAdeleRingTensorEquivInfiniteProdFinite
public import Formalism.FrobeniusOrbits.Statement
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ZsmulGeneratorEqZeroOfProjection
public import Init.Core
public import Init.Data.Function
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Ext
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Algebra.Algebra.Prod
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Prod
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Prod
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.WithAbs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.Normed.Ring.WithAbs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Finsupp.SMul
public import Mathlib.Data.Finsupp.SMulWithZero
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Free
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnn.RealComp

theorem eq_zero_of_map_eq_zero {F E A : Type} [Field F] [Field E] [Algebra F E] [CommRing A] [Algebra F A]
    {I : Type} {B : I → Type} [∀ i, CommRing (B i)] [∀ i, Algebra F (B i)] (f : ∀ i, A →ₐ[F] B i)
    (hf : ∀ a, (∀ i, f i a = 0) → a = 0) (z : A ⊗[F] E)
    (hz : ∀ i, Algebra.TensorProduct.map (f i) (AlgHom.id F E) z = 0) : z = 0 := by
  classical
  let b := Module.Free.chooseBasis F E
  have key : ∀ i (y : A ⊗[F] E) k,
      (Algebra.TensorProduct.basis (B i) b).repr (Algebra.TensorProduct.map (f i) (AlgHom.id F E) y) k =
        f i ((Algebra.TensorProduct.basis A b).repr y k) := by
    intro i y k
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a e => simp [Algebra.smul_def, mul_comm]
    | add x y hx hy => simp only [map_add (f := _), Finsupp.add_apply, hx, hy]
  apply (Algebra.TensorProduct.basis A b).repr.injective
  ext k
  rw [map_zero, Finsupp.zero_apply]
  refine hf _ fun i => ?_
  rw [← key, hz, map_zero, Finsupp.zero_apply]

theorem compInf_eq_map {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (w : InfinitePlace F) (z : AF F ⊗[F] E) : compInf F E w z =
    Algebra.TensorProduct.map (GlobalTheory.AutFunCompare.evW w) (AlgHom.id F E)
      (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

variable {D : D7}

theorem compInf_eq (w : InfinitePlace D.host.F) (z : AE D) : compInf D.host.F D.host.E w z =
    Algebra.TensorProduct.map (GlobalTheory.AutFunCompare.evW w) (AlgHom.id D.host.F D.host.E) (infPart D z) :=
  compInf_eq_map w z

theorem compInf_zero_iff (z : AE D) : (∀ w, compInf D.host.F D.host.E w z = 0) ↔ infPart D z = 0 := by
  refine ⟨fun h => ?_, fun h w => by rw [compInf_eq, h, map_zero]⟩
  exact eq_zero_of_map_eq_zero (fun w => GlobalTheory.AutFunCompare.evW w) (fun a ha => funext ha) _
    fun w => (compInf_eq w z).symm.trans (h w)

theorem theta_zero_iff {θ : InfFam D} (hθ : IsInfFam θ) (y : Ainf D.host.F ⊗[D.host.F] D.host.E) :
    (∀ τ, θ τ y = 0) ↔ y = 0 := by
  refine ⟨fun h => ?_, fun h τ => by rw [h, map_zero]⟩
  refine (GlobalTheory.Mem.VolExists.infEmb_bijective (isCMExt_host D)
    (GlobalTheory.Mem.Vol.isCMFam_host _ D.host _ D.eTau) hθ).1 (funext fun τ => ?_)
  exact (h τ).trans (map_zero _).symm

theorem infPart_conj (z : AE D) : infPart D (cA D z) = sigR (Ainf D.host.F) D.sp.cm.sig (infPart D z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem eq_zero_of_parts (z : AE D) (h1 : infPart D z = 0) (h2 : finPart D z = 0) : z = 0 := by
  obtain ⟨e, he, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  apply e.injective
  rw [map_zero]
  exact Prod.ext ((he z).1.trans h1) ((he z).2.trans h2)

theorem real_components : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → (∀ z : AE D, (∀ w, compInf D.host.F D.host.E w z = 0) ↔ ∀ τ, θ τ (infPart D z) = 0) ∧ (∀ z τ, θ τ (infPart D (cA D z)) = conj (θ τ (infPart D z))) ∧ (∀ x τ, θ τ (infPart D (incA D x)) = tauE D τ x) ∧ (∀ z : AE D, (∀ τ, θ τ (infPart D z) = 0) → finPart D z = 0 → z = 0) := by
  intro D θ hθ
  refine ⟨fun z => (compInf_zero_iff z).trans (theta_zero_iff hθ _).symm, fun z τ => ?_, fun x τ => (hθ τ).1 x,
    fun z h1 h2 => eq_zero_of_parts z ((theta_zero_iff hθ _).1 h1) h2⟩
  rw [infPart_conj]
  exact GlobalTheory.Mem.VolExists.infEmb_sigR (isCMExt_host D) (hθ τ) _

end GlobalTheory.StdUnn.RealComp

end
