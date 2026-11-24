module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardAdelicCharacterLocalComponentNeOne
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompProjAnisotropicAnisotropicEmbedding
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Classical
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.IsField
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Opposites
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Basic
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Basis
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.FieldTheory.Normal.Basic
public import Mathlib.FieldTheory.Normal.Defs
public import Mathlib.FieldTheory.Perfect
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.SesquilinearForm.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.CMField
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Ideal.Basic
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Prime
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Trace.Basic
public import Mathlib.RingTheory.Trace.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SkewPairing

theorem trace_one_tmul {F E R : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    [CommRing R] [Algebra F R] (x : E) :
    Algebra.trace R (R ⊗[F] E) ((1 : R) ⊗ₜ[F] x) = algebraMap F R (Algebra.trace F E x) := by
  rw [Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul, LinearMap.trace_baseChange]

variable {D : D7}

theorem trace_incA (x : D.host.E) :
    Algebra.trace (AF D.host.F) (AE D) (incA D x) =
      algebraMap D.host.F (AF D.host.F) (Algebra.trace D.host.F D.host.E x) :=
  trace_one_tmul x

theorem cA_smul (c : AF D.host.F) (a : AE D) : cA D (c • a) = c • cA D a := by
  induction a using TensorProduct.inductionOn with
  | tmul x y => rfl
  | add x y hx hy => rw [smul_add, map_add (f := _), map_add (f := _), hx, hy, smul_add]

theorem trace_star (x : D.host.E) :
    Algebra.trace D.host.F D.host.E (star x) = Algebra.trace D.host.F D.host.E x :=
  Algebra.trace_eq_of_algEquiv (AlgEquiv.ofBijective D.sp.cm.sig D.sp.cm.sig.bijective) x

theorem eq_zero_of_char {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {q : D.host.F}
    (h : ∀ t : AF D.host.F, ψ (t * algebraMap D.host.F (AF D.host.F) q) = 1) : q = 0 := by
  by_contra hq
  obtain ⟨I, hI, hP⟩ := Ring.not_isField_iff_exists_prime.1 (RingOfIntegers.not_isField D.host.F)
  obtain ⟨y, hy⟩ := GlobalTheory.StdCharLocal.psiV_ne_one D ψ hψ ⟨I, hP, hI⟩
  have h1 := h (pairA D.host.F 0 (singleV D.host.F ⟨I, hP, hI⟩ y) * algebraMap D.host.F (AF D.host.F) q⁻¹)
  rw [mul_assoc, ← map_mul, inv_mul_cancel₀ hq, map_one, mul_one] at h1
  exact hy h1

theorem skew_perfect : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (ρ : ℕ) (M : Matrix (Fin ρ) (Fin ρ) D.host.E), Mᴴ = -M → (∀ c : skewA D ρ, ψ (algebraMap D.host.F (AF D.host.F) (1 / 2) * Algebra.trace (AF D.host.F) (AE D) ((rat M : Mx D ρ ρ) * c.1).trace) = 1) → M = 0 := by
  intro D ψ hψ ρ M hM h
  have key : ∀ A : Matrix (Fin ρ) (Fin ρ) D.host.E, Algebra.trace D.host.F D.host.E (M * A).trace = 0 := by
    intro A
    refine eq_zero_of_char hψ fun t => ?_
    have hN : adj (rat (A - Aᴴ) : Mx D ρ ρ) = -rat (A - Aᴴ) := by
      rw [← rat_conjTranspose, ← rat_neg, conjTranspose_sub, conjTranspose_conjTranspose, neg_sub]
    have hc : t • (rat (A - Aᴴ) : Mx D ρ ρ) ∈ skewA D ρ := by
      rw [mem_skewA, ← smul_neg, ← hN]
      funext i j
      exact cA_smul t (rat (A - Aᴴ) j i)
    have h1 := h ⟨_, hc⟩
    have e1 : (M * (A - Aᴴ)).trace = (M * A).trace + star (M * A).trace := by
      rw [← trace_conjTranspose, conjTranspose_mul, hM, Matrix.mul_neg, trace_neg, trace_mul_comm Aᴴ, Matrix.mul_sub,
        trace_sub, sub_eq_add_neg]
    have e2 : ((rat M : Mx D ρ ρ) * (t • (rat (A - Aᴴ) : Mx D ρ ρ))).trace = t • incA D (M * (A - Aᴴ)).trace := by
      have hmul : (rat (M * (A - Aᴴ)) : Mx D ρ ρ) = rat M * rat (A - Aᴴ) :=
        Matrix.map_mul
      rw [Matrix.mul_smul, trace_smul, ← hmul, AddMonoidHom.map_trace (incA D)]
      rfl
    have e3 : algebraMap D.host.F (AF D.host.F) (1 / 2) * Algebra.trace (AF D.host.F) (AE D)
        ((rat M : Mx D ρ ρ) * (t • (rat (A - Aᴴ) : Mx D ρ ρ))).trace =
        t * algebraMap D.host.F (AF D.host.F) (Algebra.trace D.host.F D.host.E (M * A).trace) := by
      rw [e2, map_smul, trace_incA, e1, map_add (f := _), trace_star, smul_eq_mul, mul_left_comm, ← map_mul]
      congr 2
      ring
    rw [← e3]
    exact h1
  funext j i
  refine (traceForm_nondegenerate D.host.F D.host.E).1 (M j i) fun s => ?_
  have := key (Matrix.single i j s)
  rwa [trace_mul_single] at this

end GlobalTheory.SkewPairing
