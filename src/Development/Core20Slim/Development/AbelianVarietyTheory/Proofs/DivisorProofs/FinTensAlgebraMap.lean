module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.Divisors.PerCEmb
public import Formalism.LocalToGlobal.IndefiniteReal.ThPinsR
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.AddCharTrivialIntegralFiniteAdeleMul
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FinTensMemLatO
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Zero
public import Init.Ext
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Instances.Matrix

@[expose] public section

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory   
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.VacSign

open GlobalTheory.LatVac

variable {D : D7} {S T : HSp D}











theorem incA_smul_finTens {m n : ℕ} (x : D.host.E) (α : Af D.host.F) (M : Matrix (Fin m) (Fin n) D.host.E) :
    incA D x • finTens α M = finTens α (x • M) := by
  ext i j
  change ((1 : AF D.host.F) ⊗ₜ[D.host.F] x : AE D) * pairA D.host.F 0 α ⊗ₜ[D.host.F] M i j =
    pairA D.host.F 0 α ⊗ₜ[D.host.F] (x * M i j)
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]

theorem smul_mem_latO {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)} (c : 𝓞 D.host.E)
    {u : WO S T} (hu : u ∈ latO S T LS LT fun _ => True) :
    incA D (c : D.host.E) • u ∈ latO S T LS LT fun _ => True := by
  refine latO_induction (p := fun u => incA D (c : D.host.E) • u ∈ latO S T LS LT fun _ => True) ?_ ?_ ?_ ?_ hu
  · intro α hα M hM
    rw [incA_smul_finTens]
    exact finTens_mem_latO hα (smul_mem_latRat c hM)
  · rw [smul_zero]; exact zero_mem _
  · intro x y hx hy; rw [smul_add]; exact add_mem hx hy
  · intro x hx; rw [smul_neg]; exact neg_mem hx


theorem continuous_finTens {m n : ℕ} (M : Matrix (Fin m) (Fin n) D.host.E) :
    Continuous fun α : Af D.host.F => finTens α M := by
  have hp : Continuous fun α : Af D.host.F => pairA D.host.F 0 α := continuous_const.prodMk continuous_id
  refine continuous_pi fun i => continuous_pi fun j => ?_
  have e : (fun α : Af D.host.F => finTens α M i j) = fun α => pairA D.host.F 0 α • incA D (M i j) := by
    funext α
    change pairA D.host.F 0 α ⊗ₜ[D.host.F] M i j = pairA D.host.F 0 α • ((1 : AF D.host.F) ⊗ₜ[D.host.F] M i j)
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [e]
  exact Continuous.smul (g := fun _ : Af D.host.F => incA D (M i j)) hp continuous_const

theorem pair_tmul_smul {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (a : F) (x : E) :
    pairA F 0 (algebraMap F (Af F) a) ⊗ₜ[F] x = pairA F 0 1 ⊗ₜ[F] (a • x) := by
  rw [← TensorProduct.smul_tmul]
  congr 1
  exact Prod.ext (smul_zero _).symm (Algebra.algebraMap_eq_smul_one a)

theorem finTens_algebraMap {m n : ℕ} (a : D.host.F) (M : Matrix (Fin m) (Fin n) D.host.E) :
    finTens (algebraMap D.host.F (Af D.host.F) a) M = finTens 1 (a • M) := by
  ext i j
  change pairA D.host.F 0 (algebraMap D.host.F (Af D.host.F) a) ⊗ₜ[D.host.F] M i j =
    pairA D.host.F 0 1 ⊗ₜ[D.host.F] (a • M i j)
  exact pair_tmul_smul a (M i j)





end GlobalTheory.VacSign

end
