module

public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.LevelA
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.MeasFr
public import Formalism.LocalRingCardinality.DataCD
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.SpanPowerMembership.HaarDensityNeZero
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.HermitianColumns.InLocalDiscriminantKernel
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.MeasUpq
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.UnimodInst
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FundamentalEquivalence.AdBridge
public import Formalism.LocalToGlobal.UnitaryNorms.RealPl
public import Formalism.RealPlaceAnalysis.Complexify
public import Formalism.SatakeDualWeyl.Statement
public import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Function
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Commute.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Embedding
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SProd
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct

namespace Formalism.IndefR.Eqv

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {V : HSp D}

theorem finHom_eq_one_iff (h : GA D V) : finHom V h = 1 ↔ Lev.finE V h = 1 := by
  unfold Lev.finE
  rw [MonoidHom.comp_apply]
  refine ⟨fun h1 => by rw [h1, map_one], fun h1 => ?_⟩
  have hinj : Function.Injective (Formalism.IndefR.Lev.swapAE D) := by
    intro a b hab
    unfold Formalism.IndefR.Lev.swapAE at hab
    simpa using hab
  apply Units.ext
  ext i j
  have h2 := congrArg (fun g => (Units.val g) i j) h1
  simp only [Formalism.UG.bc, Units.coe_map, MonoidHom.coe_coe, RingHom.mapMatrix_apply, Matrix.map_apply,
    Units.val_one] at h2
  apply hinj
  refine Eq.trans h2 ?_
  by_cases hij : i = j <;> simp [Matrix.one_apply, hij]

theorem brg_mem_GinfC (fr : UI.Frames D V) (x : (UI.instV fr).GA) : UI.brg fr x ∈ GinfC V ↔ x.2 = 1 := by
  unfold GinfC
  rw [MonoidHom.mem_ker, finHom_eq_one_iff, ← Units.val_eq_one]
  have hb := (UI.brg_isBridge fr x).2
  have hz : ∀ z, Formalism.IndefR.Lev.swapAE D (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sndA D.host.F)
      (AlgHom.id D.host.F D.host.E) z) = (Algebra.TensorProduct.lift ((Algebra.TensorProduct.includeRight : Formalism.MainNotions.S.Af D.host.F →ₐ[D.host.F] D.host.E ⊗[D.host.F] Formalism.MainNotions.S.Af D.host.F).comp (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sndA D.host.F)) (Algebra.TensorProduct.includeLeft : D.host.E →ₐ[D.host.F] D.host.E ⊗[D.host.F] Formalism.MainNotions.S.Af D.host.F) (fun _ _ => Commute.all _ _)) z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => exact (map_zero _).symm
    | tmul a e => simp [Formalism.IndefR.Lev.swapAE, Algebra.TensorProduct.tmul_mul_tmul]
    | add y w hy hw => erw [map_add, map_add, hy, hw, map_add]
  have key : Units.val (Lev.finE V (UI.brg fr x)) =
      Formalism.L2.SG.AdBridge.ofHAFin (UI.instV fr) (UI.brg fr x) := by
    ext i j
    exact hz _
  rw [key]
  constructor
  · intro h1
    have h2 : (UI.instV fr).fmat x.2 = 1 := hb.trans h1
    simpa [Units.val_eq_one] using h2
  · intro h1
    have h2 : (UI.instV fr).fmat x.2 = 1 := by simp [h1]
    exact hb.symm.trans h2

theorem ginf_compact (F : MF.FrA V) (hD : V.IsDefinite) : CompactSpace (UI.instV (MF.toFrames F)).Ginf := by
  have hc : ∀ v : InfinitePlace D.host.F, CompactSpace (Formalism.REAL.UJ ((MF.toFrames F).ε v)) := by
    intro v
    haveI : CompactSpace (UpqT (V.sig (tauE D ((Formalism.L2.Host.tauPl D).symm v))).1
        (V.sig (tauE D ((Formalism.L2.Host.tauPl D).symm v))).2) := by
      rcases hD (tauE D ((Formalism.L2.Host.tauPl D).symm v)) with h | h
      · rw [h]; infer_instance
      · rw [h]; infer_instance
    exact (MF.phiR F v).toHomeomorph.compactSpace
  exact @Pi.compactSpace _ _ (fun _ => inferInstance) hc

theorem isCompact_GinfC (hS : V.SigOK) (hD : V.IsDefinite) : IsCompact (GinfC V : Set (GA D V)) := by
  obtain ⟨F⟩ := MF.frA_nonempty hS
  haveI := ginf_compact F hD
  have e : (GinfC V : Set (GA D V)) = UI.brg (MF.toFrames F) '' (Set.univ ×ˢ {1}) := by
    ext h
    obtain ⟨x, rfl⟩ := (UI.brg (MF.toFrames F)).surjective h
    rw [SetLike.mem_coe, brg_mem_GinfC]
    constructor
    · intro hx
      exact ⟨x, ⟨trivial, hx⟩, rfl⟩
    · rintro ⟨x', ⟨-, hx'⟩, e'⟩
      have := (UI.brg (MF.toFrames F)).injective e'
      subst this
      exact hx'
  rw [e]
  exact (isCompact_univ.prod isCompact_singleton).image (UI.brg (MF.toFrames F)).continuous

end Formalism.IndefR.Eqv

end
