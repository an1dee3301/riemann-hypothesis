module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCongLevelIntG
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaLatticeImageRationalHomLattice
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HESmulRight
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Rat.Basic
public import Init.Prelude
public import Init.PropLemmas
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Order.Kleene
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm

@[expose] public section

noncomputable section

open NumberField

namespace GlobalTheory.VacRead

def cE (D : Formalism.BasicNotions.D7) (cc : Ideal (𝓞 D.host.K)) : Submodule (𝓞 D.host.E) D.host.E :=
  Submodule.span (𝓞 D.host.E) {x | ∃ c ∈ cc, x = ((c : D.host.K) : D.host.E)}

def bInv (D : Formalism.BasicNotions.D7) (cc : Ideal (𝓞 D.host.K)) (r : D.host.E) : Submodule (𝓞 D.host.E) D.host.E :=
  Submodule.span (𝓞 D.host.E) {y | ∃ α ∈ cE D cc, ∃ γ ∈ cE D D.host.ccK,
    y = r * D.host.conj α * γ / (Ideal.absNorm cc : D.host.E)}

def lsB (D : Formalism.BasicNotions.D7) (cc : Ideal (𝓞 D.host.K)) (r : D.host.E) (a : ℕ) : GlobalTheory.InertSign.Lat D a :=
  Submodule.pi Set.univ fun _ => bInv D cc r

theorem mem_lsB {D : Formalism.BasicNotions.D7} {cc : Ideal (𝓞 D.host.K)} {r : D.host.E} {a : ℕ} {y : Fin a → D.host.E} :
    y ∈ lsB D cc r a ↔ ∀ i, y i ∈ bInv D cc r := by
  simp [lsB, Submodule.mem_pi]

end GlobalTheory.VacRead
