module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaPartD
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundUnitary
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermInf
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Core
public import Init.Data.Nat.Basic
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Rat
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Finsupp.SMul
public import Mathlib.Data.Finsupp.SMulWithZero
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Free
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.Trace.Defs

@[expose] public section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Phase

section Gen

variable {F E : Type} [Field F] [Field E] [Algebra F E]
variable {R S : Type} [CommRing R] [Algebra F R] [CommRing S] [Algebra F S]

theorem repr_tmap (f : R →ₐ[F] S) {ι : Type} (b : Module.Basis ι F E) (z : R ⊗[F] E) (k : ι) :
    (Algebra.TensorProduct.basis S b).repr (Algebra.TensorProduct.map f (AlgHom.id F E) z) k =
      f ((Algebra.TensorProduct.basis R b).repr z k) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r e =>
    simp [Algebra.TensorProduct.basis_repr_tmul, Finsupp.mapRange_apply, Algebra.smul_def]
  | add x y hx hy => simp [map_add (f := _), hx, hy]

theorem trace_tmap [Module.Finite F E] (f : R →ₐ[F] S) (z : R ⊗[F] E) :
    f (Algebra.trace R (R ⊗[F] E) z) =
      Algebra.trace S (S ⊗[F] E) (Algebra.TensorProduct.map f (AlgHom.id F E) z) := by
  classical
  let b := Module.Free.chooseBasis F E
  rw [Algebra.trace_eq_matrix_trace (Algebra.TensorProduct.basis R b),
    Algebra.trace_eq_matrix_trace (Algebra.TensorProduct.basis S b)]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.trace, Matrix.diag, Algebra.leftMulMatrix_eq_repr_mul, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← repr_tmap, map_mul]
  simp only [Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.map_tmul, map_one, AlgHom.coe_id, id_eq]

theorem tmap_sigR (f : R →ₐ[F] S) (σ : E →ₐ[F] E) (z : R ⊗[F] E) :
    Algebra.TensorProduct.map f (AlgHom.id F E) (sigR R σ z) =
      sigR S σ (Algebra.TensorProduct.map f (AlgHom.id F E) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => simp [sigR]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem tmap_inclR (f : R →ₐ[F] S) (e : E) :
    Algebra.TensorProduct.map f (AlgHom.id F E) (inclR R e) = inclR S e := by
  simp [inclR]

theorem tmap_gramR (f : R →ₐ[F] S) (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (X : Fin n → Fin M → R ⊗[F] E) :
    (gramR R σ J X).map (Algebra.TensorProduct.map f (AlgHom.id F E)) =
      gramR S σ J (fun a i => Algebra.TensorProduct.map f (AlgHom.id F E) (X a i)) := by
  ext a c
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.map_apply, gramR, hR, Formalism.UG.hform, JR, map_sum, map_mul, tmap_sigR, tmap_inclR]

theorem tmap_phase [Module.Finite F E] (f : R →ₐ[F] S) (σ : E →ₐ[F] E) {M n : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (B : Matrix (Fin n) (Fin n) (R ⊗[F] E))
    (X : Fin n → Fin M → R ⊗[F] E) :
    f (algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) (Matrix.trace (B * gramR R σ J X))) =
      algebraMap F S (1 / 2) * Algebra.trace S (S ⊗[F] E)
        (Matrix.trace (B.map (Algebra.TensorProduct.map f (AlgHom.id F E)) *
          gramR S σ J (fun a i => Algebra.TensorProduct.map f (AlgHom.id F E) (X a i)))) := by
  rw [map_mul, AlgHom.commutes, trace_tmap, ← tmap_gramR]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.map_apply, map_sum, map_mul]

end Gen

theorem adelic_phase_split : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
  IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (n : ℕ) (ψ : AddChar (AF F) ℂ)
  (b : HermR (AF F) σ n) (X : Fin n → Fin M → AF F ⊗[F] E),
  ψ (algebraMap F (AF F) (1 / 2) * Algebra.trace (AF F) (AF F ⊗[F] E)
      (Matrix.trace ((b : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) * gramR (AF F) σ J X))) =
    psiInf F ψ (algebraMap F (Ainf F) (1 / 2) * Algebra.trace (Ainf F) (Ainf F ⊗[F] E)
      (Matrix.trace (((hermInf σ b : HermR (Ainf F) σ n) : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) *
        gramR (Ainf F) σ J (projInf X)))) *
    psiFin F ψ (algebraMap F (Af F) (1 / 2) * Algebra.trace (Af F) (Af F ⊗[F] E)
      (Matrix.trace (((hermFin σ b : HermR (Af F) σ n) : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) *
        gramR (Af F) σ J (projFin X)))) := by
  intro F E _ _ _ _ _ σ _ M J n ψ b X
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have h1 := tmap_phase (fstA F) σ J (b : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) X
  have h2 := tmap_phase (sndA F) σ J (b : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) X
  have key : ∀ T : AF F, ψ T = psiInf F ψ (fstA F T) * psiFin F ψ (sndA F T) := by
    intro T
    simp only [psiInf, psiFin]
    rw [← AddChar.map_add_eq_mul]
    congr 1
    exact (Prod.fst_add_snd T).symm
  rw [key, h1, h2]
  rfl

end GlobalTheory.CompanionTheory.SiegelND.Integ.Phase
