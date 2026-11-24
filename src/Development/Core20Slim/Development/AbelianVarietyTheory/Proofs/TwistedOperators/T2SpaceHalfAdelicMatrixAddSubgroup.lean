module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.GinfCSecondCountable
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Nonempty
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.SetNotation
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Group.Subgroup
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Basic
public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.Sets.Compacts

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HalfAverage

variable {D : D7}

scoped instance lcAE : LocallyCompactSpace (AE D) := (Formalism.IndefR.Eqv.ae_facts D).2.2.1
scoped instance t2AE : T2Space (AE D) := (Formalism.IndefR.Eqv.ae_facts D).2.1

def halfMx (a : AE D) (m n : ℕ) : AddSubgroup (Mx D m n) where
  carrier := {t | IsHalf a t}
  add_mem' {x y} hx hy i j := by
    show a * (x i j + y i j) = x i j + y i j
    rw [mul_add, hx i j, hy i j]
  zero_mem' i j := mul_zero a
  neg_mem' {x} hx i j := by
    show a * (-x i j) = -x i j
    rw [mul_neg, hx i j]

theorem mem_halfMx {a : AE D} {m n : ℕ} {t : Mx D m n} : t ∈ halfMx a m n ↔ IsHalf a t := Iff.rfl

theorem isClosed_halfMx (a : AE D) (m n : ℕ) : IsClosed (halfMx a m n : Set (Mx D m n)) := by
  have : (halfMx a m n : Set (Mx D m n)) = ⋂ i, ⋂ j, {t : Mx D m n | a * t i j = t i j} := by
    ext t; simp only [SetLike.mem_coe, mem_halfMx, IsHalf, Set.mem_iInter, Set.mem_setOf_eq]
  rw [this]
  exact isClosed_iInter fun i => isClosed_iInter fun j =>
    isClosed_eq (continuous_const.mul ((continuous_apply j).comp (continuous_apply i)))
      ((continuous_apply j).comp (continuous_apply i))

scoped instance lcMx (m n : ℕ) : LocallyCompactSpace (Mx D m n) :=
  inferInstanceAs (LocallyCompactSpace (Fin m → Fin n → AE D))

scoped instance tagMx (m n : ℕ) : IsTopologicalAddGroup (Mx D m n) :=
  inferInstanceAs (IsTopologicalAddGroup (Fin m → Fin n → AE D))

scoped instance t2Mx (m n : ℕ) : T2Space (Mx D m n) :=
  inferInstanceAs (T2Space (Fin m → Fin n → AE D))

scoped instance tagHalf (a : AE D) (m n : ℕ) : IsTopologicalAddGroup (halfMx a m n) :=
  inferInstance

scoped instance t2Space_halfAdelicMatrixAddSubgroup (a : AE D) (m n : ℕ) : T2Space (halfMx a m n) := inferInstance

scoped instance lcHalf (a : AE D) (m n : ℕ) : LocallyCompactSpace (halfMx a m n) :=
  (isClosed_halfMx a m n).isClosedEmbedding_subtypeVal.locallyCompactSpace

scoped instance measHalf (a : AE D) (m n : ℕ) : MeasurableSpace (halfMx a m n) := borel _

scoped instance borelHalf (a : AE D) (m n : ℕ) : BorelSpace (halfMx a m n) := ⟨rfl⟩

def haarHalf (a : AE D) (m n : ℕ) : Measure (halfMx a m n) := Measure.addHaar

instance (a : AE D) (m n : ℕ) : (haarHalf a m n).IsAddHaarMeasure := by
  unfold haarHalf; infer_instance

def restEmb (V W : HSp D) {r : ℕ} (K : Matrix (Fin r) (Fin V.rank) D.host.E) (t : Mx D W.rank r) : WO V W :=
  HMul.hMul (t : Matrix (Fin W.rank) (Fin r) (AE D)) (K.map (incA D))

def avgForm (ψ : AddChar (AF D.host.F) ℂ) (V V' W : HSp D) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E)
    (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E) (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r))
    (K : Matrix (Fin r) (Fin V.rank) D.host.E) (e : AE D) (ℓ' : (WO V' W → ℂ) →ₗ[ℂ] ℂ) (f : WO V W → ℂ) : ℂ :=
  ∫ t : halfMx (cA D e) W.rank r,
    ℓ' (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 (heisO ψ V W (restEmb V W K t) f)) ∂haarHalf (cA D e) W.rank r

end GlobalTheory.HalfAverage

namespace GlobalTheory.HalfAverage

variable {D : D7}

theorem isHalf_mul {a : AE D} {m n k : ℕ} {t : Mx D m n} (ht : IsHalf a t) (M : Matrix (Fin n) (Fin k) (AE D)) :
    IsHalf a (HMul.hMul t M : Mx D m k) := fun i j => by
  simp only [Matrix.mul_apply, Finset.mul_sum, ← mul_assoc, ht i _]

theorem mul_isHalf {a : AE D} {m n : ℕ} {t : Mx D m n} (ht : IsHalf a t) (M : Matrix (Fin m) (Fin m) (AE D)) :
    IsHalf a (HMul.hMul M t : Mx D m n) := fun i j => by
  simp only [Matrix.mul_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by rw [mul_left_comm, ht k j]

def leftMul (a : AE D) {m n : ℕ} (M : Matrix (Fin m) (Fin m) (AE D)) (t : halfMx a m n) : halfMx a m n :=
  ⟨HMul.hMul M (t : Mx D m n), mul_isHalf t.2 M⟩

theorem leftMul_coe (a : AE D) {m n : ℕ} (M : Matrix (Fin m) (Fin m) (AE D)) (t : halfMx a m n) :
    (leftMul a M t : Mx D m n) = HMul.hMul M (t : Mx D m n) := rfl

theorem restEmb_add (V W : HSp D) {r : ℕ} (K : Matrix (Fin r) (Fin V.rank) D.host.E) (t t' : Mx D W.rank r) :
    restEmb V W K (t + t') = restEmb V W K t + restEmb V W K t' := Matrix.add_mul _ _ _

end GlobalTheory.HalfAverage
