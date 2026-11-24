module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSBExtFunEqHalfInd
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulMemLatO
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Insert
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.FinPl
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPl.LatIndHalf

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]





theorem mul_mem_latV {S : HSp D} {L : Lat S} {P : Pl D → Prop} {w : AE D} (hw : finPart D w ∈ intAE D)
    {y : Fin S.rank → AE D} (hy : y ∈ latV S L P) : (fun i => w * y i) ∈ latV S L P := by
  let Ψ : (Fin S.rank → AE D) →+ (Fin S.rank → AE D) :=
    AddMonoidHom.mk' (fun y i => w * y i) fun a b => funext fun i => mul_add w (a i) (b i)
  have main : latV S L P ≤ (latV S L P).comap Ψ := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨β, hβi, hβ, a, ha, x, hx, rfl⟩
    rw [Set.mem_singleton_iff] at ha
    subst ha
    let Φ : Af D.host.F ⊗[D.host.F] D.host.E →+ (Fin S.rank → AE D) :=
      AddMonoidHom.mk' (fun c i => GlobalTheory.LatticeStable.liftFin D (c * (β ⊗ₜ[D.host.F] (1 * x i))))
        fun c c' => funext fun i => by rw [add_mul, LinearMap.map_add (f := _)]; rfl
    have hle : intAE D ≤ (latV S L P).comap Φ := by
      refine (AddSubgroup.closure_le _).2 ?_
      rintro _ ⟨γ, hγ, o, rfl⟩
      refine AddSubgroup.subset_closure ⟨γ * β, fun v => by rw [map_mul]; exact mul_mem (hγ v) (hβi v),
        fun v hv => by rw [map_mul, hβ v hv, mul_zero], 1, rfl, o • x, L.smul_mem o hx, ?_⟩
      funext i
      change GlobalTheory.LatticeStable.liftFin D ((γ ⊗ₜ[D.host.F] (o : D.host.E)) * (β ⊗ₜ[D.host.F] (1 * x i))) = _
      rw [Algebra.TensorProduct.tmul_mul_tmul, GlobalTheory.LatticeStable.liftFin_tmul, Pi.smul_apply, Algebra.smul_def,
        show algebraMap (𝓞 D.host.E) D.host.E o = (o : D.host.E) from rfl]
      congr 1
      ring
    have e : Ψ (fun i => pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 * x i)) = Φ (finPart D w) :=
      funext fun i => GlobalTheory.LatticeStable.mul_pair_tmul D w β _
    rw [SetLike.mem_coe, AddSubgroup.mem_comap, e]
    exact hle hw
  exact main hy

variable {p : SplitPt D k} {S T : HSp D} {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']



end GlobalTheory.FinPl.LatIndHalf


end
