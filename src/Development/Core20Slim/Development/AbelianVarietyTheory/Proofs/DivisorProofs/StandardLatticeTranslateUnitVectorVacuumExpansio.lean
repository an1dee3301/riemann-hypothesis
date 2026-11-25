module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetVecEq
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualSkewIdealLatticeIsSelfDualStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutes
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaSpaceSelfDualPairAtMostLineStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTaylorCoeffsAlgebraicAtComplexMultiplicatio
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.VacuumUnderAdelicPairModulusOne
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Lemmas
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Quotient
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.NNRat.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Quot
public import Mathlib.Data.Rat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.GroupTheory.Coset.Defs
public import Mathlib.GroupTheory.Finiteness
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.GroupTheory.Index
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

noncomputable section

namespace GlobalTheory.FunObj.TransExp

theorem hf_swap (D : D7) (T : Tor D) {N N' : ℕ} (x y : VC D N N') :
    Hf D T y x = (starRingEnd ℂ) (Hf D T x y) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Hf, map_div₀, map_sum, map_mul, Complex.conj_conj, Complex.conj_ofReal]
  congr 1
  exact Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ =>
    Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem wd_comm (D : D7) (T : Tor D) {N N' : ℕ} (x y : VC D N N') (F : VC D N N' → ℂ)
    (z : VC D N N') : Wd D T x (Wd D T y F) z = Formalism.MainNotions.TaylorLogMetric.kap D T x y * Wd D T y (Wd D T x F) z := by
  have key : Complex.exp (-(Real.pi : ℂ) * Hf D T x y) =
      Formalism.MainNotions.TaylorLogMetric.kap D T x y * Complex.exp (-(Real.pi : ℂ) * Hf D T y x) := by
    rw [Formalism.MainNotions.TaylorLogMetric.kap, ← Complex.exp_add, hf_swap D T x y]
    congr 1
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im] <;> ring
  have e1 : ∀ u v c : ℂ, Complex.exp (-(Real.pi : ℂ) * (u + v) - c) =
      Complex.exp (-(Real.pi : ℂ) * u - c) * Complex.exp (-(Real.pi : ℂ) * v) := by
    intro u v c; rw [← Complex.exp_add]; congr 1; ring
  simp only [Wd, U, VacMove.hf_add_left]
  rw [show z + y + x = z + x + y from add_right_comm _ _ _, e1 (Hf D T z y) (Hf D T x y),
    e1 (Hf D T z x) (Hf D T y x), key]
  ring

theorem wd_mul_sum (D : D7) (T : Tor D) {N N' : ℕ} {ι : Type*} (x : VC D N N') (c : ℂ) (s : Finset ι)
    (f : ι → VC D N N' → ℂ) (z : VC D N N') :
    Wd D T x (fun w => c * ∑ q ∈ s, f q w) z = c * ∑ q ∈ s, Wd D T x (f q) z := by
  simp only [Wd, U, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun q _ => by ring

theorem wd_iop_of (D : D7) (T : Tor D) {N N' : ℕ} (A B : AddSubgroup (VC D N N')) (e0 : VC D N N' → ℂ)
    (x : VC D N N') (hB : ∀ y ∈ B, ∀ F, Wd D T y F = fun z => al D T y * U D T y F z)
    (hfix : Wd D T x e0 = e0) :
    Wd D T x (Iop D T A B e0) = fun z => ((Real.sqrt ((A.addSubgroupOf B).index : ℝ))⁻¹ : ℂ) *
      ∑ᶠ q : B ⧸ A.addSubgroupOf B, Formalism.MainNotions.TaylorLogMetric.kap D T x ((Quotient.out q : B) : VC D N N') *
        Wd D T ((Quotient.out q : B) : VC D N N') e0 z := by
  have hI : Iop D T A B e0 = fun z => ((Real.sqrt ((A.addSubgroupOf B).index : ℝ))⁻¹ : ℂ) *
      ∑ᶠ q : B ⧸ A.addSubgroupOf B, Wd D T ((Quotient.out q : B) : VC D N N') e0 z := by
    funext z
    unfold Iop
    congr 1
    refine finsum_congr fun q => ?_
    rw [hB _ (Quotient.out q).2]
  funext z
  rw [hI]
  by_cases h0 : (A.addSubgroupOf B).index = 0
  · simp [Wd, U, h0]
  · haveI : Finite (B ⧸ A.addSubgroupOf B) := Nat.finite_of_card_ne_zero h0
    haveI := Fintype.ofFinite (B ⧸ A.addSubgroupOf B)
    simp only [finsum_eq_sum_of_fintype]
    rw [wd_mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [wd_comm, hfix]

theorem wd_iop_expand : ∀ (D : D7) (δ : ℂ), Crv D ⊤ δ → ∀ (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ≠ ⊥ → ∀ {a d : ℕ} (e0 : VC D a d → ℂ), e0 ∈ Th D (tor0 D ⊤ δ) (stdL D a) (stdL D d) → ∀ x ∈ (La0 D (tor0 D ⊤ δ) a d), Wd D (tor0 D ⊤ δ) x (Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)) e0) = fun z => ((Real.sqrt (((La0 D (tor0 D ⊤ δ) a d).addSubgroupOf (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d))).index : ℝ))⁻¹ : ℂ) * ∑ᶠ q : (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)) ⧸ (La0 D (tor0 D ⊤ δ) a d).addSubgroupOf (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)), Formalism.MainNotions.TaylorLogMetric.kap D (tor0 D ⊤ δ) x ((Quotient.out q : (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d))) : VC D a d) * Wd D (tor0 D ⊤ δ) ((Quotient.out q : (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d))) : VC D a d) e0 z := by
  intro D δ hc 𝔪 h𝔪 a d e0 he x hx
  have h1 := (GlobalTheory.InducedType.induced_type D).1
  have k0 : KLat D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) :=
    VacMove.klat _ (VacMove.moves_one D a) (VacMove.moves_one D d)
  have kp : KLat D (tor0 D ⊤ δ) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)) :=
    Or.inr ⟨_, _, VacMove.sd_of_moves (VacMove.moves_one D a), GlobalTheory.T.selfDualSkewIdealLattice_isSelfDual D 𝔪 d h𝔪, rfl⟩
  exact wd_iop_of D _ _ _ e0 x (GlobalTheory.T.theta_space_selfDual_pair_at_most_line D h1 ⊤ δ hc a d _ kp).2.1 (VacMove.wd_fix h1 hc k0 he hx)

end GlobalTheory.FunObj.TransExp
