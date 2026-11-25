module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsApprox
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralActionUnitCharacterEigen
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaLiftIdempotentForm
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitCharTriangle
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAdelicPointUnitaryGroupGramOne
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardLatticeDoubleCosetClassesStabilisers
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHalfIdem
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.HermitianColumns.InLocalDiscriminantKernel
public import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.SatakeDualWeyl.Statement
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Function
public import Init.Data.Int.Basic
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.Tactic.LinearCombination.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

open NumberField IsDedekindDomain
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 lamOf Th La Iop Qbar lamC)
open Formalism.MainNotions.StandardLatticesGL3 (TT stdL pt oddE0 Wd La0 Crv inc OhE IntU)
open GlobalTheory.NormSum (Pair intG)
open GlobalTheory.FunObj.SqNum (hatId CongOne skewLat unitBlock cosetVec)
open GlobalTheory.NormExact (Reads Setup IsFinIdl HasFinPart finPt)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (InId IsUnitDet unitChar stdFst)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdRead

noncomputable section

namespace GlobalTheory.StdRead.IntLift

open GlobalTheory.BotClassDict (finQ)
open GlobalTheory.UnitaryMove (ct blockUnit)

theorem adjugate_mem {A : Type} [CommRing A] (O : Subring A) {n : ℕ} (N : Matrix (Fin n) (Fin n) A)
    (hN : ∀ i j, N i j ∈ O) (i j : Fin n) : N.adjugate i j ∈ O := by
  let M : Matrix (Fin n) (Fin n) O := Matrix.of fun i j => ⟨N i j, hN i j⟩
  have e : N = O.subtype.mapMatrix M := rfl
  rw [e, ← RingHom.map_adjugate]
  exact (M.adjugate i j).2

theorem exists_block {A : Type} [CommRing A] (c : A →+* A) (hc : ∀ a, c (c a) = a) (O : Subring A) (hO : ∀ a ∈ O, c a ∈ O)
    {ε w : A} (h1 : ε * ε = ε) (h2 : ε * c ε = 0) (hε : ε ∈ O) (hw : w ∈ O) {n : ℕ} (N : Matrix (Fin n) (Fin n) A)
    (hN : ∀ i j, N i j ∈ O) (hd : ε * (w * N.det) = ε) :
    ∃ K K' : Matrix (Fin n) (Fin n) A, K * K' = 1 ∧ K' * K = 1 ∧ ct c K = K' ∧ (∀ i j, K i j ∈ O ∧ K' i j ∈ O) ∧
      ∀ i j, ε * K' i j = ε * N i j := by
  have hP : ∀ i j, (w • N.adjugate) i j ∈ O := fun i j => mul_mem hw (adjugate_mem O N hN i j)
  have hPQ : ε • ((w • N.adjugate) * N) = ε • (1 : Matrix (Fin n) (Fin n) A) := by
    rw [Matrix.smul_mul, Matrix.adjugate_mul, smul_smul, smul_smul, mul_assoc, hd]
  have hQP : ε • (N * (w • N.adjugate)) = ε • (1 : Matrix (Fin n) (Fin n) A) := by
    rw [Matrix.mul_smul, Matrix.mul_adjugate, smul_smul, smul_smul, mul_assoc, hd]
  generalize w • N.adjugate = P at hP hPQ hQP
  obtain ⟨a, b, d⟩ := blockUnit c hc h1 h2 P N hPQ hQP
  have hf : 1 - ε - c ε ∈ O := sub_mem (sub_mem (one_mem _) hε) (hO _ hε)
  have hone : ∀ i j, (1 : Matrix (Fin n) (Fin n) A) i j ∈ O := fun i j => by
    by_cases h : i = j <;> simp [Matrix.one_apply, h]
  refine ⟨_, _, a, b, d, fun i j => ⟨?_, ?_⟩, fun i j => ?_⟩
  · exact add_mem (add_mem (mul_mem hf (hone i j)) (mul_mem hε (hP i j))) (mul_mem (hO _ hε) (hO _ (hN j i)))
  · exact add_mem (add_mem (mul_mem hf (hone i j)) (mul_mem hε (hN i j))) (mul_mem (hO _ hε) (hO _ (hP j i)))
  · simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    linear_combination (N i j - (1 : Matrix (Fin n) (Fin n) A) i j) * h1 +
      (ct c P i j - (1 : Matrix (Fin n) (Fin n) A) i j) * h2

theorem toE_injective (D : D7) : Function.Injective (toE D) :=
  (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).injective.comp (GlobalTheory.BotFormula.toAfE D).injective

theorem exists_lift : ∀ {D : D7} (e : AE D) (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS →
  ∀ {a : ℕ} (N : Matrix (Fin a) (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D)), (∀ i j, N i j ∈ OhE D) →
  ∀ x : (AE D)ˣ, IsUnitDet e (N.map (toE D)) x → ∃ k : Formalism.MainNotions.StandardLatticesGL3.GA D a, k ∈ intG D a ∧
    ∀ i j, GlobalTheory.BotClassDict.finQ D e * (((k : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D))⁻¹ : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D)) :
      Matrix (Fin a) (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D)) i j = GlobalTheory.BotClassDict.finQ D e * N i j := by
  intro D e SS he a N hN x hx
  obtain ⟨-, hx1, hx2⟩ := hx
  have hdet : (N.map (toE D)).det = toE D N.det := (RingHom.map_det (toE D) _).symm
  have h1 := CharVal.eps_idem he
  have hxe : finQ D (x : AE D) = 1 - finQ D e + finQ D e * N.det := toE_injective D (by
    rw [CharVal.toE_finQ, hx1, hdet, RingHom.map_add (f := _), RingHom.map_sub, RingHom.map_mul, RingHom.map_one, CharVal.toE_finQ])
  have hxx : finQ D (x : AE D) * finQ D ((x⁻¹ : (AE D)ˣ) : AE D) = 1 := by
    rw [← RingHom.map_mul, Units.mul_inv, RingHom.map_one]
  have hd : finQ D e * (finQ D ((x⁻¹ : (AE D)ˣ) : AE D) * N.det) = finQ D e := by
    rw [hxe] at hxx
    linear_combination finQ D e * hxx + (finQ D ((x⁻¹ : (AE D)ˣ) : AE D) * (1 - N.det)) * h1
  obtain ⟨K, K', a1, a2, a3, a4, a5⟩ := exists_block (Formalism.MainNotions.StandardLatticesGL3.sgA D) (GlobalTheory.NormSum.VacMove.sgA_sgA D) (OhE D)
    (fun _ h => GlobalTheory.NormSum.VacMove.sgA_mem D h) h1 (CharVal.eps_conj he) (CharVal.eps_int he) (CharVal.finQ_int hx2) N hN hd
  let u : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D) := ⟨K, K', a1, a2⟩
  have hu : u ∈ Formalism.MainNotions.StandardLatticesGL3.GA D a := by
    change Formalism.UG.cT _ K * _ * K = _
    rw [Matrix.map_one _ (map_zero _) (map_one _), mul_one]
    exact (congrArg (· * K) a3).trans a2
  exact ⟨⟨u, hu⟩, (GlobalTheory.NormSum.mem_intG _).2 a4, a5⟩

end GlobalTheory.StdRead.IntLift

end
