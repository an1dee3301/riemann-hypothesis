module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.WeilFull
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilOperatorLatticeStabiliserFixesVacuumNonsplit
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemCompletedHomLatticeIffFrameStabiliserAction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsEtaTildeUnramified
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitaryOnTheta
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulMemLatO
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexNeZeroOfFinite
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumFixesVacuumNonSplitPlaceUnramifiedStatement
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.SpanPowerMembership.LocAtA
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.HermitianColumns.InLocalDiscriminantKernel
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Function
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Even
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Lattice.Basic
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Tactic.LinearCombination.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.InertAll

theorem nonSplitAt_of_forall (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (ε : AF D.host.F) (hε : IsPlaceIdem D v ε)
    (hns : ∀ e, IsSplitIdem D e → e * algebraMap (AF D.host.F) (AE D) ε = 0) : GlobalTheory.WeilParts.NonSplitAt D v ε := by
  refine ⟨hε, fun ⟨e, he, heq⟩ => ?_⟩
  have k := hns e he
  have e0 : e = 0 := by
    rw [← heq, mul_add, he.1, he.2.1, add_zero] at k
    exact k
  rw [e0, map_zero, zero_add] at heq
  obtain ⟨α, rfl, h1, -⟩ := hε
  have hinj : Function.Injective (algebraMap (AF D.host.F) (AE D)) :=
    Algebra.TensorProduct.includeLeft_injective (S := D.host.F) (algebraMap D.host.F D.host.E).injective
  have : pairA D.host.F 0 α = 0 := hinj (by rw [map_zero]; exact heq.symm)
  have : α = 0 := congrArg Prod.snd this
  rw [this, map_zero] at h1
  exact zero_ne_one h1

theorem unramAt_of_unrAtV (D : D7) (ε : AF D.host.F) (χ : (AE D)ˣ →* Circle) (hχ : Formalism.IndefR.WeilFull.UnrAtV ε χ) : GlobalTheory.WeilParts.UnramAt ε χ :=
  fun x hx i1 i2 => hχ x (by linear_combination (-1 : AE D) * hx) i1 i2

theorem inertAllO_of_eta (D : D7) (hη : ∃ η, GlobalTheory.WeilParts.IsEtaTilde D η) : Formalism.IndefR.WeilFull.InertAllO D := by
  intro ψ S T χS χT om H _ _ ΛS ΛT hS hT βS βT hβS hβT v ε hε _ hns uS uT g h sg sh hg hh f hf hvac
  have hv : GlobalTheory.WeilParts.NonSplitAt D v ε := nonSplitAt_of_forall D v ε hε hns
  have hst : ∀ u, u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun w => w = v) ↔
      actO S T g h u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun w => w = v) :=
    fun u => GlobalTheory.LatStab.mem_latO_iff_actO_mem D S T ΛS ΛT βS βT hS.1 hT.1 hβS hβT g h hg hh _ u
  have hfix : ∀ u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun w => w = v),
      heisO ψ S T u f = f := by
    intro u hu
    obtain ⟨a, ha, ha2⟩ := GlobalTheory.FinWeilO.exists_half_of_nonSplit hv
    have h1 : 2 • (a • u) = u := by
      rw [two_nsmul, ← add_smul, ← two_mul, ha2, GlobalTheory.VecInvInert.idem_smul_eq hε hu]
    have h2 := hvac.1 (a • u) (GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ a ha u hu)
    rwa [h1] at h2
  exact GlobalTheory.T.weilDatum_fixes_vacuum_nonSplitPlace_unramified D ψ H.std S T ΛS ΛT hS hT χS χT om hη H v ε hv (unramAt_of_unrAtV D ε χS uS) (unramAt_of_unrAtV D ε χT uT) g h sg sh hst f hf hfix

theorem inertAllO : ∀ D : D7, Formalism.IndefR.WeilFull.InertAllO D :=
  fun D => inertAllO_of_eta D (GlobalTheory.WeilParts.exists_isEtaTilde_unramified D)

end GlobalTheory.InertAll
