module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittCoreEmbeddingPreservesSupportedUnitarySubgro
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.LinearCombination.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace Matrix

namespace GlobalTheory.IwaPlace.BuildQ

variable {D : D7}


theorem adj_diagonal {n : ℕ} (f : Fin n → AE D) :
    adj (Matrix.diagonal f) = Matrix.diagonal (fun i => cA D (f i)) := by
  ext i j; simp [adj, Matrix.diagonal_apply]; split_ifs <;> simp_all [eq_comm]



end GlobalTheory.IwaPlace.BuildQ

namespace GlobalTheory.IwaPlace.BuildQ

variable {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ)


end GlobalTheory.IwaPlace.BuildQ

namespace GlobalTheory.IwaPlace.BuildQ

variable {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ)

theorem smul_eq_of_mem {P : Pl D → Prop} {ε : AE D} (hε : ∀ a, a ∈ idAt D P ↔ ε * a = a)
    {m n : ℕ} {x : Mx D m n} (hx : ∀ i j, x i j ∈ idAt D P) : ε • x = x := by
  ext i j; rw [Matrix.smul_apply, smul_eq_mul, (hε _).1 (hx i j)]

theorem one_sub_mul_self {ε : AE D} (hεε : ε * ε = ε) : (1 - ε) * ε = 0 := by
  rw [sub_mul, one_mul, hεε, sub_self]

theorem one_sub_sq {ε : AE D} (hεε : ε * ε = ε) : (1 - ε) * (1 - ε) = 1 - ε := by
  rw [mul_sub, mul_one, one_sub_mul_self hεε, sub_zero]


theorem diag_absorb {ε : AE D} {n : ℕ} {α : Fin n → AE D} (hαε : ∀ i, ε * α i = α i) :
    ε • Matrix.diagonal α = Matrix.diagonal α := by
  ext i j
  simp only [Matrix.smul_apply, Matrix.diagonal_apply, smul_eq_mul]
  split_ifs with h
  · exact hαε i
  · rw [mul_zero]

theorem diag_const {ε : AE D} {n : ℕ} {α β : Fin n → AE D} (hαβ : ∀ i, α i * β i = ε) :
    (Matrix.diagonal fun i => α i * β i) = ε • (1 : Mx D n n) := by
  have : (fun i => α i * β i) = fun _ => ε := funext hαβ
  rw [this]
  ext i j
  by_cases h : i = j
  · subst h; simp
  · simp [h]


end GlobalTheory.IwaPlace.BuildQ

namespace GlobalTheory.IwaPlace.BuildQ

variable {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ)








end GlobalTheory.IwaPlace.BuildQ

namespace GlobalTheory.IwaPlace.BuildQ

variable {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ)



theorem smul_shift {ε : AE D} (hεε : ε * ε = ε) {m n : ℕ} {x : Mx D m n} (hx : ε • x = x) (y : Mx D m n) :
    ε • (x + (1 - ε) • y - y) = x + (1 - ε) • y - y := by
  have e : x + (1 - ε) • y - y = x - ε • y := by
    rw [sub_smul, one_smul]; abel
  rw [e, smul_sub, hx, smul_smul, hεε]

theorem scalar_X {R : Type*} [CommRing R] {ε a b x y : R} (ha : ε * a = a) (hab : a * b = ε) (hx : ε * x = x) :
    a * (x * b + (1 - ε) * y) = x := by
  linear_combination x * hab + hx - y * ha

end GlobalTheory.IwaPlace.BuildQ


