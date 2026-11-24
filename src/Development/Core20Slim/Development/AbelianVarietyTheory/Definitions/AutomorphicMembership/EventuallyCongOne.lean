module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompactAdele
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.LocalToGlobal.Columns.CoefColLemmas
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks
public import Formalism.LocalRingCardinality.DataCoeff
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedBessel
public import Formalism.LocalToGlobal.ProjectiveLattices.OneLtAbsNormReal
public import Formalism.SatakeDualWeyl.Statement
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Units.Lemmas
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Complex.BigOperators
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.NNRat.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Rat.Init
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Maximal
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Col Formalism.L2.DIV  GlobalTheory.Mem GlobalTheory.Mem.Col2  Matrix
open Formalism.L2.Theta Formalism.MainNotions.StandardLattice GlobalTheory.Mem.Th Filter Topology
open Formalism.IndefR.Lev (finE swapAE EAf)
open scoped TensorProduct

namespace GlobalTheory.Mem.ColAd

section Tr

variable {ι : Type} [Fintype ι] {n : ℕ} (G : ι → Matrix (Fin n) (Fin n) ℂ)











end Tr

section Val

variable {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] {n : ℕ}
  (S : GStep E K n) (emb : ι → E →+* K) (σ : K →+* ℂ)




variable {S emb σ} {lam : ι → DomWeight n} {φ : S.Cl → Fr emb σ n → ℂ}








end Val

section Comp

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (θ : InfF D) (V : HSp D) {n : ℕ} (hn : V.rank = n) {ι : Type} (t : ι ≃ D.what₂.Tau)




variable {V}











theorem isAniso_of_gram (hG : V.gram = 1) : IsAniso V := by
  rintro r C ⟨hr, hC, h0⟩
  have h1 := congrFun (congrFun h0 ⟨0, hr⟩) ⟨0, hr⟩
  rw [hG, Matrix.mul_one, Matrix.mul_apply] at h1
  have h2 := congrArg D.host.φ₀ h1
  have h3 : ∀ a : D.host.E, D.host.φ₀ (star a) = starRingEnd ℂ (D.host.φ₀ a) := D.sp.cm.cmUnram.2.1 _
  have h4 : ∑ i, Complex.normSq (D.host.φ₀ (C i ⟨0, hr⟩)) = 0 := by
    apply Complex.ofReal_injective
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum] at h2
    rw [Complex.ofReal_sum, Complex.ofReal_zero, ← map_zero D.host.φ₀]
    refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) h2
    rw [map_mul, Complex.normSq_eq_conj_mul_self, ← h3]
    rfl
  refine hC.ne_zero ⟨0, hr⟩ (funext fun i => ?_)
  have := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => Complex.normSq_nonneg _).1 h4 i (Finset.mem_univ i)
  simpa using this


end Comp

end GlobalTheory.Mem.ColAd

end
