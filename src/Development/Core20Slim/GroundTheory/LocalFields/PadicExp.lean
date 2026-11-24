module

public import Mathlib
public import Development.Core20Slim.GroundTheory.LocalFields.PadicLogHom

@[expose] public section

namespace GroundTheory.LocalField

open ValuativeRel IsLocalRing Topology Filter
open scoped WithZero

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

section ExpLog

variable (p : ℕ) [hp : Fact p.Prime] [CharP 𝓀[K] p] [CharZero K]





end ExpLog

section Iso


theorem mem_integer_of_mem_valBall {n : ℤ} (hn : 0 ≤ n) {x : K} (hx : x ∈ valBall (K := K) n) :
    x ∈ 𝒪[K] := by
  rw [← normalizedValuation_le_one_iff]
  exact hx.trans (by rw [← WithZero.exp_zero, WithZero.exp_le_exp]; omega)



variable (p : ℕ) [hp : Fact p.Prime] [CharP 𝓀[K] p] [CharZero K]












end Iso

end GroundTheory.LocalField
