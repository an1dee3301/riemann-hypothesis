module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.SatakeParameters.EqZeroOfForallLeExp
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CompletionExistence.LeOneIffOfMulEqOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Init.Core
public import Init.Data.Function
public import Init.Data.Int.Basic
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.WithOne.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Order.Monoid.TypeTags
public import Mathlib.Algebra.Order.Monoid.Unbundled.TypeTags
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.CMField
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Lattice
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.Topology.Algebra.Valued.ValuationTopology
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.DenseEmbedding
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.UniformSpace.Defs
public import ReciprocityTheory.Automorphisms.SplitCoeAlgebraMap
public import ReciprocityTheory.Automorphisms.Unitary

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SplitCompl

theorem exists_ringEquiv : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (s : SplitPlace L),
    ∃ i : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L, Continuous i ∧ Continuous i.symm ∧
      ∀ x : L, i (s.i x) = algebraMap L (s.w.adicCompletion L) x := by
  intro L _ _ _ s

  have hf : ∀ x : L, Valued.v (s.i.toRingHom x) = s.w.valuation L x :=
    fun x => PI.CompAtExist.muV_eq s x
  obtain ⟨φ, hφc, hφ, -⟩ := GlobalTheory.DenseCompl.exists_extension s.w s.v (f := s.i.toRingHom) hf

  let g : maximalRealSubfield L →+* s.w.adicCompletion L :=
    (algebraMap L (s.w.adicCompletion L)).comp (algebraMap (maximalRealSubfield L) L)
  have hg : ∀ a, Valued.v (g a) = s.v.valuation (maximalRealSubfield L) a := by
    intro a
    simp only [g, RingHom.comp_apply]
    rw [GlobalTheory.Idele.valued_algebraMap, ← PI.CompAtExist.muV_eq s, PI.CompAtExist.muV_apply, AlgHom.commutes,
      GlobalTheory.Idele.valued_algebraMap]
  obtain ⟨ψ, hψc, hψ, -⟩ := GlobalTheory.DenseCompl.exists_extension s.v s.w g hg
  have hcomp : ∀ y, φ (ψ y) = y := by
    intro y
    refine (HeightOneSpectrum.denseRange_algebraMap (maximalRealSubfield L) s.v).induction_on
      (p := fun y => φ (ψ y) = y) y (isClosed_eq (hφc.comp hψc) continuous_id) fun a => ?_
    rw [hψ]
    simp only [g, RingHom.comp_apply]
    rw [hφ]
    exact s.i.commutes a
  have hsurj : Function.Surjective φ := fun y => ⟨ψ y, hcomp y⟩
  let e := RingEquiv.ofBijective φ ⟨φ.injective, hsurj⟩
  have he : ∀ y, e.symm y = ψ y := fun y => e.injective (by rw [e.apply_symm_apply]; exact (hcomp y).symm)
  refine ⟨e.symm, ?_, ?_, fun x => ?_⟩
  · exact hψc.congr fun y => (he y).symm
  · exact hφc
  · have h := e.symm_apply_apply (algebraMap L (s.w.adicCompletion L) x)
    exact (congrArg e.symm (hφ x)).symm.trans h

end GlobalTheory.SplitCompl
