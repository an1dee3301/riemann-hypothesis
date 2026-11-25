module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermOf
public import Init.Classical
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Fin.Basic
public import Init.Data.Fin.Lemmas
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Basic
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Module.Submodule.Map
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Basic
public import Mathlib.Algebra.Order.Kleene
public import Mathlib.Algebra.Quotient
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.GroupTheory.Index
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.BoundedOrder.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Defs
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.Bialgebra.Basic
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.SummationFilter
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped Matrix

section Lat

variable (K : Type) [Field K] [NumberField K]

def intVec (m : ℕ) : Submodule (𝓞 K) (Fin m → K) where
  carrier := {v | ∀ i, ∃ o : 𝓞 K, algebraMap (𝓞 K) K o = v i}
  add_mem' := by
    intro v w hv hw i
    obtain ⟨o, ho⟩ := hv i
    obtain ⟨p, hp⟩ := hw i
    exact ⟨o + p, by simp [ho, hp]⟩
  zero_mem' := fun _ => ⟨0, by simp⟩
  smul_mem' := by
    intro a v hv i
    obtain ⟨o, ho⟩ := hv i
    exact ⟨a * o, by simp [ho, Algebra.smul_def]⟩

abbrev FQ : Type := (Fin 1 → K) ⧸ intVec K 1

def den (x : K) : Ideal (𝓞 K) :=
  Ideal.torsionOf (𝓞 K) (FQ K) (Submodule.Quotient.mk fun _ => x)

def idx (c : Submodule (𝓞 K) K) : ℕ :=
  (1 : Submodule (𝓞 K) K).toAddSubgroup.relIndex c.toAddSubgroup

def zetaR (r : ℝ) : ℝ := ∑' I : Ideal (𝓞 K), (Ideal.absNorm I : ℝ) ^ (-r)

variable {K}

def lam {m : ℕ} (c : Matrix (Fin m) (Fin m) K) : Submodule (𝓞 K) (Fin m → K) :=
  intVec K m ⊔ (intVec K m).map (c.mulVecLin.restrictScalars (𝓞 K))

def IsLat {m : ℕ} (L : Submodule (𝓞 K) (Fin m → K)) : Prop :=
  L.FG ∧ Submodule.span K (L : Set (Fin m → K)) = ⊤

def tor {m : ℕ} (c : Matrix (Fin m) (Fin m) K) (u : Fin m → K) : Ideal (𝓞 K) :=
  Ideal.torsionOf (𝓞 K) ((Fin m → K) ⧸ lam c) (Submodule.Quotient.mk u)

def lastFib {m : ℕ} (C : Matrix (Fin (m + 1)) (Fin (m + 1)) K) : Submodule (𝓞 K) K :=
  (lam C).comap (LinearMap.single (𝓞 K) (fun _ : Fin (m + 1) => K) (Fin.last m))

theorem isLat_intVec (m : ℕ) : IsLat (intVec K m) := by
  refine ⟨?_, ?_⟩
  · have h : intVec K m = (⊤ : Submodule (𝓞 K) (Fin m → 𝓞 K)).map
        (LinearMap.compLeft (Algebra.linearMap (𝓞 K) K) (Fin m)) := by
      ext v
      simp only [Submodule.mem_map, Submodule.mem_top, true_and]
      constructor
      · intro hv
        choose o ho using hv
        exact ⟨o, funext fun i => ho i⟩
      · rintro ⟨o, rfl⟩ i
        exact ⟨o i, rfl⟩
    rw [h]
    exact Submodule.FG.map _ Module.Finite.fg_top
  · rw [eq_top_iff]
    intro v _
    have hv : v = ∑ i, v i • (Pi.single i (1 : K) : Fin m → K) := by
      ext j
      simp [Finset.sum_apply, Pi.single_apply]
    rw [hv]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    intro j
    by_cases h : j = i
    · subst h
      exact ⟨1, by simp⟩
    · exact ⟨0, by simp [Pi.single_apply, h]⟩

end Lat

section GlobalTheory

variable {F E : Type} [Field F] [Field E] [Algebra F E]

def blk {m : ℕ} (σ : E →ₐ[F] E) (c : Matrix (Fin m) (Fin m) E) (u : Fin m → E) (d : E) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) E := fun i j =>
  Fin.lastCases (motive := fun _ => E)
    (Fin.lastCases (motive := fun _ => E) d (fun b => σ (u b)) j)
    (fun a => Fin.lastCases (motive := fun _ => E) (u a) (fun b => c a b) j) i

variable [NumberField E]

def sO (σ : E →ₐ[F] E) : 𝓞 E →+* 𝓞 E := RingOfIntegers.mapRingHom (σ : E →+* E)

end GlobalTheory

end GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
