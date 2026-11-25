module

public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.NullSecKAlg
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.MapDomainFlpFlp
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.HopPderivComm
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.FockMomOfBasic
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.NullStable
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.PderivComm
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.MomLin
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.NullSec
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.FockMono
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.NullStableAlt
public import Init.Core
public import Init.Data.Function
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Logic.Function.Defs
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic

@[expose] public section

namespace PositivityTheory.Rg.Sw.LC

private theorem nullSec_add' {m n : ℕ} {ε : Fin m → Bool} {c : ℝ} (hc : 0 < c) {P Q : PX m n}
    (hP : NullSec ε c P) (hQ : NullSec ε c Q) : NullSec ε c (P + Q) := by
  intro R hR
  rw [mul_add, (momLin m n c hc (R * P) (R * Q) 1).1, hP R hR, hQ R hR, add_zero]

private theorem nullSec_smul' {m n : ℕ} {ε : Fin m → Bool} {c : ℝ} (hc : 0 < c) {P : PX m n}
    (r : ℂ) (hP : NullSec ε c P) : NullSec ε c (r • P) := by
  intro R hR
  rw [mul_smul_comm, (momLin m n c hc (R * P) 0 r).2, hP R hR, mul_zero]

private theorem nullSec_fock_apply_of_mem_kAlg {m n : ℕ} {ε : Fin m → Bool} {c : ℝ} (hc : 0 < c)
    (w : Module.End ℂ (PX m n)) (hw : w ∈ kAlg ε) :
    ∀ p : PX m n, NullSec ε c (fock c p) → NullSec ε c (fock c (w p)) := by
  have hlin := (fockBasic m n c hc).1
  obtain ⟨a₁, a₂, a₃, a₄, a₅, hk⟩ := fockK_of fockBasic m n ε c hc
  have hN := nullStable m n ε c hc
  have hw' : w ∈ Algebra.adjoin ℂ (Set.range fun ij : Fin n × Fin n => KopL ε ij.1 ij.2) := hw
  clear hw
  induction hw' using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨⟨i, j⟩, rfl⟩ := hx
    intro p hp
    show NullSec ε c (fock c (KopL ε i j p))
    rw [hk i j p]
    obtain ⟨h1, h2, h3, h4⟩ := hN i j _ hp
    exact nullSec_add' hc (nullSec_add' hc (nullSec_add' hc (nullSec_add' hc
      (nullSec_smul' hc _ h4) (nullSec_smul' hc _ h1)) (nullSec_smul' hc _ h2))
      (nullSec_smul' hc _ h3)) (nullSec_smul' hc _ hp)
  | algebraMap r =>
    intro p hp
    rw [Module.algebraMap_end_apply, hlin.map_smul]
    exact nullSec_smul' hc r hp
  | add x y _ _ hx hy =>
    intro p hp
    rw [LinearMap.add_apply, hlin.map_add (f := _)]
    exact nullSec_add' hc (hx p hp) (hy p hp)
  | mul x y _ _ hx hy =>
    intro p hp
    exact hx _ (hy p hp)

theorem lc_of_core (hC : CoreLC) : PositivityTheory.Rg.Sw.LC := by
  intro m n ε c hc lam hlam P hP
  obtain ⟨hlin, hbij, -⟩ := fockBasic m n c hc
  let F : PX m n →ₗ[ℂ] PX m n := hlin.mk' _
  let Λ : PX m n →ₗ[ℂ] ℂ := lam.comp F
  have hΛ : ∀ (a b : Fin m) (p : PX m n), Λ (Dop ε c a b p) = 0 := by
    intro a b p
    show lam (fock c (Dop ε c a b p)) = 0
    rw [← fockHOp_of fockBasic m n ε c hc a b p]
    exact hlam a b _
  obtain ⟨p, rfl⟩ := hbij.2 P
  obtain ⟨w, hw, hval⟩ := hC m n ε c hc Λ hΛ p
  have h1 : lam (fock c p) = contr c (w p) := hval
  rw [h1]
  have hM := fockMom_of_basic fockBasic m n c hc
  have h0 : mom c (fock c (w p)) = 0 := by
    simpa using nullSec_fock_apply_of_mem_kAlg hc w hw p hP 1 (Subalgebra.one_mem _)
  rw [hM.2] at h0
  exact (mul_eq_zero.mp h0).resolve_left hM.1

end PositivityTheory.Rg.Sw.LC
