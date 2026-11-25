import Std

namespace Erdos406

/-- At index zero we read the units digit. Higher indices read successive base-three digits. -/
def DigitFree (n : Nat) : Prop :=
  ∀ j : Nat, (2 ^ n / 3 ^ j) % 3 ≠ 2


/-- The finiteness question, expressed as boundedness of the exceptional
    natural exponents. The results in this project are partial theorems. -/
def FinitenessConjecture : Prop := ∃ B : Nat, ∀ n, DigitFree n → n ≤ B

/-- Erdős's stronger proposed classification. -/
def SharpConjecture : Prop := ∀ n : Nat, DigitFree n ↔ n = 0 ∨ n = 2 ∨ n = 8

private def acceptedOrWitnessed (n : Nat) : Bool :=
  n == 0 || n == 2 || n == 8 ||
  (List.range 22).any (fun j => (2 ^ n / 3 ^ j) % 3 == 2)

set_option exponentiation.threshold 10100 in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem certificate :
    (List.range 101).all (fun q =>
      (List.range (min 100 (10001 - 100 * q))).all (fun r => acceptedOrWitnessed (100 * q + r))) = true := by
  decide

private theorem free_of_bound {n b : Nat}
    (h : ∀ j : Fin b, (2 ^ n / 3 ^ (j : Nat)) % 3 ≠ 2)
    (hb : 2 ^ n < 3 ^ b) : DigitFree n := by
  intro j
  by_cases hj : j < b
  · exact h ⟨j, hj⟩
  · have hbj : b ≤ j := by omega
    have hp : 3 ^ b ≤ 3 ^ j := Nat.pow_le_pow_right (by decide) hbj
    rw [Nat.div_eq_of_lt (Nat.lt_of_lt_of_le hb hp)]
    decide

/-- A witness, when required, always occurs within the lowest 22 digits. -/
theorem exception_or_low_digit (n : Nat) (hn : n ≤ 10000) :
    (n = 0 ∨ n = 2 ∨ n = 8) ∨ ∃ j < 22, (2 ^ n / 3 ^ j) % 3 = 2 := by
  have hq : n / 100 ∈ List.range 101 := List.mem_range.mpr (by omega)
  have hr : n % 100 ∈ List.range (min 100 (10001 - 100 * (n / 100))) :=
    List.mem_range.mpr (by omega)
  have row := List.all_eq_true.mp certificate (n / 100) hq
  have hc := List.all_eq_true.mp row (n % 100) hr
  have hn' : 100 * (n / 100) + n % 100 = n := by omega
  rw [hn'] at hc
  simpa [acceptedOrWitnessed, List.any_eq_true, or_assoc] using hc

set_option exponentiation.threshold 2000 in
/-- The uniform 22-digit bound is sharp in this interval. -/
theorem first_two_at_21 :
    (∀ j : Fin 21, (2 ^ 1134 / 3 ^ (j : Nat)) % 3 ≠ 2) ∧
    (2 ^ 1134 / 3 ^ 21) % 3 = 2 := by decide

theorem digitFree_iff_of_le_10000 (n : Nat) (hn : n ≤ 10000) :
    DigitFree n ↔ n = 0 ∨ n = 2 ∨ n = 8 := by
  constructor
  · intro h
    rcases exception_or_low_digit n hn with hexc | ⟨j, _, hj⟩
    · exact hexc
    · exact (h j hj).elim
  · rintro (rfl | rfl | rfl)
    · exact free_of_bound (b := 1) (by decide) (by decide)
    · exact free_of_bound (b := 2) (by decide) (by decide)
    · exact free_of_bound (b := 6) (by decide) (by decide)

end Erdos406

#print axioms Erdos406.digitFree_iff_of_le_10000
