module

public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.NullStableAlt
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.NullSec
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.FockMono
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.List.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Sum.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.GroupWithZero.Action
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Module.Submodule.Range
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Derivation
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.MvPolynomial.Supported
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Dedup
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Lattice.Basic
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Function
public import Mathlib.Data.Set.Operations
public import Mathlib.Data.Sum.Basic
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Hom.Basic
public import Mathlib.Order.SetNotation
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.Tactic.Abel

@[expose] public section

noncomputable section

open MvPolynomial

namespace PositivityTheory.Rg.Sw.LC

open PositivityTheory.Rg.Sw

variable {m n : ℕ}

def inF1 (ε : Fin m → Bool) (k : Fin m × Fin n × Bool) : Prop := k.2.2 = !ε k.1

instance (ε : Fin m → Bool) : DecidablePred (inF1 (n := n) ε) := fun k => by unfold inF1; infer_instance

def F1 (ε : Fin m → Bool) : Submodule ℂ (PX m n) := Subalgebra.toSubmodule (MvPolynomial.supported ℂ {k | inF1 ε k})

def F2 (ε : Fin m → Bool) : Submodule ℂ (PX m n) := Subalgebra.toSubmodule (MvPolynomial.supported ℂ {k | ¬ inF1 ε k})

def rdeg (ε : Fin m → Bool) (s : Fin m × Fin n × Bool →₀ ℕ) (a : Fin m) : ℕ := ∑ i, s (a, i, !ε a)

def box (ε : Fin m → Bool) (R : Set (Fin m → ℕ)) : Submodule ℂ (PX m n) :=
  Submodule.span ℂ {p | ∃ s : Fin m × Fin n × Bool →₀ ℕ, (∀ k ∈ s.support, inF1 ε k) ∧ rdeg ε s ∈ R ∧ p = monomial s 1}

def wt (c : ℝ) (s : Fin m × Fin n × Bool →₀ ℕ) : ℝ := ∏ k ∈ s.support, ((s k).factorial : ℝ) * (2 * c) ^ (s k)

def fform (c : ℝ) (p q : PX m n) : ℂ := ∑ s ∈ p.support ∪ q.support, star (p.coeff s) * q.coeff s * (wt c s : ℂ)

def D1 (ε : Fin m → Bool) (c : ℝ) (a b : Fin m) (p : PX m n) : PX m n :=
  if ε a = ε b then
    (if ε a then -∑ i, X (a, i, false) * pderiv (b, i, false) p else ∑ i, X (b, i, true) * pderiv (a, i, true) p)
  else
    (if ε a then -(1 / (2 * c) : ℂ) • ∑ i, X (a, i, false) * X (b, i, true) * p
     else (2 * c : ℂ) • ∑ i, pderiv (b, i, false) (pderiv (a, i, true) p))

def D2 (ε : Fin m → Bool) (c : ℝ) (a b : Fin m) (p : PX m n) : PX m n :=
  if ε a = ε b then
    (if ε a then ∑ i, X (b, i, true) * pderiv (a, i, true) p else -∑ i, X (a, i, false) * pderiv (b, i, false) p)
  else
    (if ε a then (2 * c : ℂ) • ∑ i, pderiv (b, i, false) (pderiv (a, i, true) p)
     else -(1 / (2 * c) : ℂ) • ∑ i, X (a, i, false) * X (b, i, true) * p)

def firstFamilyOperatorEnd (ε : Fin m → Bool) (c : ℝ) (a b : Fin m) : Module.End ℂ (PX m n) where
  toFun := D1 ε c a b
  map_add' p q := by unfold D1; split_ifs <;> simp [mul_add, Finset.sum_add_distrib, smul_add] <;> abel
  map_smul' r p := by unfold D1; split_ifs <;> simp [Finset.mul_sum, Finset.smul_sum, smul_comm r, mul_smul_comm]

abbrev Sym (m n : ℕ) := MvPolynomial ((Fin m × Fin n × Bool) ⊕ (Fin m × Fin n × Bool)) ℂ

def opMono (t : (Fin m × Fin n × Bool) ⊕ (Fin m × Fin n × Bool) →₀ ℕ) (f : PX m n) : PX m n :=
  monomial (t.comapDomain Sum.inl Sum.inl_injective.injOn) 1 *
    (((Finset.univ : Finset (Fin m × Fin n × Bool)).toList.map fun k => (pderiv (R := ℂ) k).toLinearMap ^ (t (Sum.inr k))).prod) f

def op (s : Sym m n) (f : PX m n) : PX m n := ∑ t ∈ s.support, s.coeff t • opMono t f

def SymbolInFirstFamily (ε : Fin m → Bool) (s : Sym m n) : Prop := ∀ t ∈ s.support, ∀ k, (t (Sum.inl k) ≠ 0 ∨ t (Sum.inr k) ≠ 0) → inF1 ε k

def symK (ε : Fin m → Bool) (i j : Fin n) : Derivation ℂ (Sym m n) (Sym m n) :=
  MvPolynomial.mkDerivation ℂ (Sum.elim
    (fun k => if ε k.1 then (if k.2.2 = false ∧ k.2.1 = j then X (Sum.inl (k.1, i, false)) else 0)
      else (if k.2.2 = true ∧ k.2.1 = i then -X (Sum.inl (k.1, j, true)) else 0))
    (fun k => if ε k.1 then (if k.2.2 = false ∧ k.2.1 = i then -X (Sum.inr (k.1, j, false)) else 0)
      else (if k.2.2 = true ∧ k.2.1 = j then X (Sum.inr (k.1, i, true)) else 0)))

def SemiFam : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (φ : V → V → ℂ),
    (∀ v, ∀ w₁ w₂, φ v (w₁ + w₂) = φ v w₁ + φ v w₂) → (∀ v w (r : ℂ), φ v (r • w) = r * φ v w) →
    (∀ v w, φ w v = star (φ v w)) → (∀ v, v ≠ 0 → 0 < (φ v v).re) →
    ∀ (ι : Type) (T : ι → Module.End ℂ V), (∀ i, ∃ j, ∀ v w, φ (T i v) w = φ v (T j w)) →
      (∀ v, ∃ v₀ w, v = v₀ + w ∧ (∀ i, T i v₀ = 0) ∧ w ∈ ⨆ i, LinearMap.range (T i)) ∧
      ∀ v, (∀ i, T i v = 0) → v ∈ (⨆ i, LinearMap.range (T i)) → v = 0

def Bicomm : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (φ : V → V → ℂ),
    (∀ v, ∀ w₁ w₂, φ v (w₁ + w₂) = φ v w₁ + φ v w₂) → (∀ v w (r : ℂ), φ v (r • w) = r * φ v w) →
    (∀ v w, φ w v = star (φ v w)) → (∀ v, v ≠ 0 → 0 < (φ v v).re) →
    ∀ (ι : Type) (T : ι → Module.End ℂ V), (∀ i, ∃ j, ∀ v w, φ (T i v) w = φ v (T j w)) →
      ∀ x : Module.End ℂ V, (∀ t : Module.End ℂ V, (∀ i, t * T i = T i * t) → x * t = t * x) →
        x ∈ Algebra.adjoin ℂ (Set.range T)

def Dens : Prop :=
  ∀ (m n : ℕ) (ε : Fin m → Bool) (R : Finset (Fin m → ℕ)) (T : PX m n →ₗ[ℂ] PX m n), (∀ f ∈ box ε (R : Set _), T f ∈ F1 ε) →
    ∃ s : Sym m n, SymbolInFirstFamily ε s ∧ ∀ f ∈ box ε (R : Set _), op s f = T f

def SymKComm : Prop :=
  ∀ (m n : ℕ) (ε : Fin m → Bool) (i j : Fin n) (s : Sym m n), SymbolInFirstFamily ε s → ∀ f ∈ F1 ε,
    op (symK ε i j s) f = KopL ε i j (op s f) - op s (KopL ε i j f)

def InvOp : Prop :=
  PositivityTheory.Rg.Sw.FFT → ∀ (m n : ℕ) (ε : Fin m → Bool) (c : ℝ), 0 < c → ∀ s : Sym m n, SymbolInFirstFamily ε s → (∀ i j, symK ε i j s = 0) →
    ∃ w ∈ Algebra.adjoin ℂ (Set.range fun ab : Fin m × Fin m => firstFamilyOperatorEnd (n := n) ε c ab.1 ab.2), ∀ f ∈ F1 ε, op s f = w f

def RepB : Prop :=
  ∀ (m n : ℕ) (ε : Fin m → Bool) (c : ℝ), 0 < c → ∀ Λ : PX m n →ₗ[ℂ] ℂ, (∀ a b p, Λ (Dop ε c a b p) = 0) →
    ∃ B : Module.End ℂ (PX m n), (∀ R : Set (Fin m → ℕ), ∀ f ∈ box ε R, B f ∈ box ε R) ∧
      (∀ f ∈ F1 ε, ∀ g ∈ F2 ε, Λ (f * g) = contr c (B f * g)) ∧
      ∀ a b, ∀ f ∈ F1 ε, B (D1 ε c a b f) = D1 ε c a b (B f)

def FormFacts : Prop :=
  ∀ (m n : ℕ) (ε : Fin m → Bool) (c : ℝ), 0 < c →
    (∀ p q : PX m n, fform c q p = star (fform c p q)) ∧ (∀ p : PX m n, p ≠ 0 → 0 < (fform c p p).re) ∧
    (∀ (i j : Fin n) (p q : PX m n), fform c (KopL ε i j p) q = fform c p (KopL ε j i q)) ∧
    (∀ (i j : Fin n) (R : Set (Fin m → ℕ)), ∀ f ∈ box ε R, KopL ε i j f ∈ box ε R) ∧
    (∀ (i j : Fin n) (s t : Sym m n), fform (m := m) (n := n) (1 / 2) 0 0 = 0 ∧
      (∑ u ∈ (symK ε i j s).support ∪ t.support, star ((symK ε i j s).coeff u) * t.coeff u *
          ((∏ k ∈ u.support, ((u k).factorial : ℂ))) =
        ∑ u ∈ s.support ∪ (symK ε j i t).support, star (s.coeff u) * (symK ε j i t).coeff u *
          ((∏ k ∈ u.support, ((u k).factorial : ℂ)))))

end PositivityTheory.Rg.Sw.LC
