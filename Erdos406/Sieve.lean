import Erdos406.Digits

namespace ErdosLift

/-- The exact cofactor after lifting `4` through one power of three. -/
private theorem cube_step (d u : Nat) :
    (1 + (3*d)*u)^3 = 1 + (3*(3*d))*(u + 3*(d*u*u + d*d*u*u*u)) := by
  simp only [show (3 : Nat) = 1+1+1 from rfl, Nat.pow_succ, Nat.pow_zero,
    Nat.mul_add, Nat.add_mul, Nat.one_mul, Nat.mul_one]
  ac_rfl

/-- In particular, `3^(k+1)` is the exact power of 3 dividing `2^(2*3^k)-1`. -/
theorem exact_lift (k : Nat) :
    ∃ u : Nat, u % 3 = 1 ∧ 2^(2*3^k) = 1 + 3^(k+1)*u := by
  induction k with
  | zero => exact ⟨1, rfl, rfl⟩
  | succ k ih =>
    obtain ⟨u, hu, hpow⟩ := ih
    let d := 3^k
    refine ⟨u + 3*(d*u*u + d*d*u*u*u), ?_, ?_⟩
    · omega
    · calc
        2^(2*3^(k+1)) = (2^(2*3^k))^3 := by
          rw [← Nat.pow_mul, Nat.pow_succ 3 k, Nat.mul_assoc]
        _ = (1 + (3*d)*u)^3 := by dsimp [d]; rw [hpow, Nat.pow_succ 3 k]; ac_rfl
        _ = 1 + (3*(3*d))*(u + 3*(d*u*u + d*d*u*u*u)) := cube_step d u
        _ = _ := by dsimp [d]; rw [Nat.pow_succ 3 (k+1), Nat.pow_succ 3 k]; ac_rfl

theorem exact_lift_normalized (k : Nat) :
    ∃ t : Nat, 2^(2*3^k) = 1 + 3^(k+1)*(1+3*t) := by
  obtain ⟨u, hu, he⟩ := exact_lift k
  refine ⟨u / 3, ?_⟩
  have h : u = 1 + 3*(u/3) := by omega
  calc
    2^(2*3^k) = 1 + 3^(k+1)*u := he
    _ = _ := congrArg (fun z => 1 + 3^(k+1)*z) h

/-- Every suffix of k+1 ternary digits repeats with period 2 · 3^k. -/
theorem suffix_period (k a : Nat) :
    2^(a + 2*3^k) % 3^(k+1) = 2^a % 3^(k+1) := by
  obtain ⟨u, _, he⟩ := exact_lift k
  rw [Nat.pow_add, he, Nat.mul_add, Nat.mul_one]
  have h : 2^a * (3^(k+1)*u) = 3^(k+1)*(2^a*u) := by ac_rfl
  rw [h, Nat.add_mul_mod_self_left]

theorem many_periods (k a r : Nat) :
    2^(a + r*(2*3^k)) % 3^(k+1) = 2^a % 3^(k+1) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Nat.succ_mul, ← Nat.add_assoc, suffix_period, ih]

/-- Each actual fixed-width ternary suffix occurs at arbitrarily large exponents. -/
theorem suffix_recurs (k a bound : Nat) :
    ∃ n > bound, 2^n % 3^(k+1) = 2^a % 3^(k+1) := by
  refine ⟨a + (bound+1)*(2*3^k), ?_, many_periods k a (bound+1)⟩
  have h : 0 < 3^k := Nat.pow_pos (by decide)
  have hp : 0 < 2*3^k := by omega
  have hm := Nat.le_mul_of_pos_right (bound+1) hp
  omega

/-- In particular, arbitrarily large exponents pass any fixed suffix test
    for digits from {0,1}: their suffix is 00…001. -/
theorem all_zero_then_one_recurs (k bound : Nat) :
    ∃ n > bound, 2^n % 3^(k+1) = 1 := by
  obtain ⟨n, hn, he⟩ := suffix_recurs k 0 bound
  refine ⟨n, hn, ?_⟩
  have hp : 0 < 3^k := Nat.pow_pos (by decide)
  have hm : 1 < 3^(k+1) := by rw [Nat.pow_succ]; omega
  exact he.trans (Nat.mod_eq_of_lt hm)

end ErdosLift

namespace Erdos406.Suffix

/-- Powers whose units digit can be 1, indexed by their half-exponent. -/
def value (s : Nat) : Nat := 2 ^ (2 * s)

theorem units (s : Nat) : value s % 3 = 1 := by
  induction s with
  | zero => decide
  | succ s ih =>
    unfold value at *
    rw [Nat.mul_succ, Nat.pow_add, Nat.mul_mod, ih]

/-- A shift by 3^k leaves the last k+1 digits unchanged and rotates
    the next digit 0 → 1 → 2 → 0. -/
theorem rotate (k s : Nat) :
    let p := 3 ^ (k+1)
    value (s + 3^k) % p = value s % p ∧
    (value (s + 3^k) / p) % 3 = ((value s / p) % 3 + 1) % 3 := by
  dsimp only
  let p := 3^(k+1)
  obtain ⟨u, hu, hpow⟩ := ErdosLift.exact_lift k
  have he : value (s + 3^k) = value s + p*(value s*u) := by
    unfold value
    rw [Nat.mul_add, Nat.pow_add, hpow, Nat.mul_add, Nat.mul_one]
    dsimp [p]
    ac_rfl
  change value (s + 3^k) % p = value s % p ∧ _
  rw [he]
  refine ⟨Nat.add_mul_mod_self_left _ _ _, ?_⟩
  have hp : 0 < p := Nat.pow_pos (by decide)
  change ((value s + p*(value s*u)) / p) % 3 = _
  rw [Nat.add_mul_div_left _ _ hp, Nat.add_mod, Nat.mul_mod, hu, units]

/-- Among the three lifts, every possible next digit occurs:
    in particular exactly one of the three is 2. -/
theorem choose_digit (k s d : Nat) (hd : d < 3) :
    ∃ t ∈ [s, s + 3^k, s + 3^k + 3^k],
      value t % 3^(k+1) = value s % 3^(k+1) ∧
      (value t / 3^(k+1)) % 3 = d := by
  obtain ⟨h₁, h₂⟩ := rotate k s
  obtain ⟨h₃, h₄⟩ := rotate k (s+3^k)
  by_cases h : (value s / 3^(k+1)) % 3 = d
  · exact ⟨s, by simp, rfl, h⟩
  by_cases h' : (value (s+3^k) / 3^(k+1)) % 3 = d
  · exact ⟨s+3^k, by simp, h₁, h'⟩
  exact ⟨s + 3^k + 3^k, by simp, h₃.trans h₁, by omega⟩

/-- Every width-(k+1) suffix ending in 1 occurs in the first 3^k even
    powers. The other k digits are prescribed arbitrarily. -/
theorem every_suffix (k a : Nat) (ha : a < 3^(k+1)) (h₀ : a % 3 = 1) :
    ∃ s < 3^k, value s % 3^(k+1) = a := by
  induction k generalizing a with
  | zero =>
    have ha' : a < 3 := ha
    rw [Nat.mod_eq_of_lt ha'] at h₀
    subst a
    exact ⟨0, by decide, by decide⟩
  | succ k ih =>
    let p := 3^(k+1)
    have hp : 0 < p := Nat.pow_pos (by decide)
    have h3 : 3 ∣ p := ⟨3^k, by dsimp [p]; rw [Nat.pow_succ, Nat.mul_comm]⟩
    obtain ⟨s, hs, he⟩ := ih (a % p) (Nat.mod_lt _ hp) (by
      rw [Nat.mod_mod_of_dvd _ h3]; exact h₀)
    have ha' : a < p*3 := by simpa only [Nat.pow_succ 3 (k+1)] using ha
    have hq : a / p < 3 := (Nat.div_lt_iff_lt_mul hp).mpr (by simpa [Nat.mul_comm] using ha')
    obtain ⟨t, ht, hlo, hhi⟩ := choose_digit k s (a/p) hq
    refine ⟨t, ?_, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      rw [Nat.pow_succ]
      omega
    · change value t % (3^(k+1+1)) = a
      rw [Nat.pow_succ 3 (k+1), Nat.mod_mul, hlo, he, hhi]
      exact Nat.mod_add_div a p

/-- Every ternary suffix ending in 1 also occurs beyond every proposed
    bound on the exponent. -/
theorem every_suffix_recurs (k a bound : Nat) (ha : a < 3^(k+1)) (h₀ : a % 3 = 1) :
    ∃ n > bound, 2^n % 3^(k+1) = a := by
  obtain ⟨s, _, hs⟩ := every_suffix k a ha h₀
  obtain ⟨n, hn, he⟩ := ErdosLift.suffix_recurs k (2*s) bound
  exact ⟨n, hn, he.trans hs⟩

end Erdos406.Suffix

namespace Erdos406.Count

open Classical in
/-- Number of naturals `i < n` satisfying `P`. -/
noncomputable def tallyAux (P : Nat → Prop) : Nat → Nat
  | 0 => 0
  | n+1 => tallyAux P n + if P n then 1 else 0

@[simp] theorem tally_zero (P : Nat → Prop) : tallyAux P 0 = 0 := rfl

theorem tally_mono (P : Nat → Prop) {a b : Nat} (h : a ≤ b) :
    tallyAux P a ≤ tallyAux P b := by
  induction h with
  | refl => exact Nat.le_refl _
  | step h ih => rw [tallyAux]; omega

/-- A list containing every accepted offset bounds the count on the interval.
The certificates in the list need not be distinct. -/
theorem tally_cover (P : Nat → Prop) (start len : Nat) (xs : List Nat)
    (cover : ∀ i, i < len → P (start + i) → i ∈ xs) :
    tallyAux P (start + len) ≤ tallyAux P start + xs.length := by
  induction len generalizing xs with
  | zero => simp
  | succ len ih =>
    rw [Nat.add_succ, tallyAux]
    by_cases h : P (start + len)
    · have hmem := cover len (by omega) h
      have hrest := ih (xs.erase len) (fun i hi hp =>
        (List.mem_erase_of_ne (by omega : i ≠ len)).mpr (cover i (by omega) hp))
      have hlength := List.length_erase_of_mem hmem
      have hpos : 0 < xs.length := by cases xs <;> simp_all
      simp only [if_pos h]
      omega
    · simpa only [if_neg h, Nat.add_zero] using ih xs (fun i hi => cover i (by omega))

end Erdos406.Count

namespace Erdos406.Count
open Erdos406.Suffix

/-- The ternary digit immediately above a suffix of k+1 digits. -/
private def next (k s : Nat) := (value s / 3^(k+1)) % 3

private def lifts (k s : Nat) :=
  [s, s+3^k, s+3^k+3^k].filter (fun t => next k t != 2)

private theorem length_lifts (k s : Nat) : (lifts k s).length = 2 := by
  obtain ⟨_, h₁⟩ := rotate k s
  obtain ⟨_, h₂⟩ := rotate k (s+3^k)
  change next k (s+3^k) = (next k s + 1)%3 at h₁
  change next k (s+3^k+3^k) = (next k (s+3^k) + 1)%3 at h₂
  have h : next k s < 3 := Nat.mod_lt _ (by decide)
  have : next k s = 0 ∨ next k s = 1 ∨ next k s = 2 := by omega
  rcases this with h | h | h <;> simp [lifts, h₂, h₁, h]

/-- At depth k we keep the half-exponent residues modulo 3^k that
    have passed the first k+1 digit tests. -/
def candidates : Nat → List Nat
  | 0 => [0]
  | k+1 => (candidates k).bind (lifts k)

private theorem length_children (k : Nat) (l : List Nat) :
    (l.bind (lifts k)).length = l.length*2 := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.bind_cons, List.length_append, length_lifts, ih, List.length_cons,
      Nat.succ_mul]
    omega

theorem length_candidates (k : Nat) : (candidates k).length = 2^k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [candidates, length_children, ih, Nat.pow_succ]

private theorem digit_repeats (k s : Nat) :
    next k (s % 3^(k+1)) = next k s := by
  let p := 3^(k+1)
  let r := s % p
  have he := ErdosLift.many_periods (k+1) (2*r) (s / p)
  have hsplit : 2*r + s/p*(2*p) = 2*s := by
    calc
      2*r + s/p*(2*p) = 2*(r+p*(s/p)) := by rw [Nat.mul_add]; ac_rfl
      _ = 2*s := congrArg (2*·) (Nat.mod_add_div s p)
  change 2^(2*r + s/p*(2*p)) % 3^(k+1+1) = value r % 3^(k+1+1) at he
  rw [hsplit] at he
  change (value r / p)%3 = (2^(2*s) / p)%3
  rw [← Nat.mod_mul_right_div_self (value r) p 3, ← Nat.mod_mul_right_div_self (2^(2*s)) p 3]
  apply congrArg (· / p)
  simpa only [Nat.pow_succ 3 (k+1)] using he.symm

private theorem mem_candidates (s k : Nat) (h : DigitFree (2*s)) :
    s % 3^k ∈ candidates k := by
  induction k with
  | zero => simp [candidates, Nat.mod_one]
  | succ k ih =>
    apply List.mem_bind.mpr
    refine ⟨s % 3^k, ih, List.mem_filter.mpr ⟨?_, ?_⟩⟩
    · rw [Nat.pow_succ, Nat.mod_mul]
      have hq := Nat.mod_lt (s/3^k) (by decide : 0 < 3)
      have : s/3^k%3 = 0 ∨ s/3^k%3 = 1 ∨ s/3^k%3 = 2 := by omega
      rcases this with h | h | h <;> simp [h, Nat.mul_two, Nat.add_assoc]
    · have hx : next k s ≠ 2 := h (k+1)
      simpa [digit_repeats] using hx

theorem even_of_free (n : Nat) (h : DigitFree n) : n = 2*(n/2) := by
  have hn := h 0
  have ho : 2^(2*(n/2)+1) % 3 = 2 := by
    rw [Nat.pow_succ, Nat.mul_mod]
    change (value (n/2) % 3 * (2%3))%3 = 2
    rw [Erdos406.Suffix.units]
  simp only [Nat.pow_zero, Nat.div_one] at hn
  apply Classical.byContradiction
  intro hne
  have : n = 2*(n/2)+1 := by omega
  exact hn ((congrArg (fun t : Nat => 2^t % 3) this).trans ho)

private theorem cover (k q i : Nat) (hi : i < 2*3^k)
    (h : DigitFree (q*(2*3^k)+i)) :
    i ∈ (candidates k).map (fun s => 2*s) := by
  let n := q*(2*3^k)+i
  have he : n = 2*(n/2) := even_of_free n h
  have hc := mem_candidates (n/2) k (he ▸ h)
  refine List.mem_map.mpr ⟨(n/2) % 3^k, hc, ?_⟩
  calc
    2*(n/2 % 3^k) = (2*(n/2)) % (2*3^k) := (Nat.mul_mod_mul_left _ _ _).symm
    _ = n % (2*3^k) := congrArg (· % (2*3^k)) he.symm
    _ = i := by dsimp [n]; rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hi]

end Erdos406.Count

namespace Erdos406.Count

private theorem ratio (m : Nat) : m * 2^(2*m) ≤ 3^(2*m) := by
  have h : m ≤ 2^m := by
    induction m with
    | zero => decide
    | succ m ih =>
      rw [Nat.pow_succ]
      have hp := Nat.pow_pos (n := m) (by decide : 0 < 2)
      omega
  calc
    m * 2^(2*m) ≤ 2^m * 2^(2*m) := Nat.mul_le_mul_right _ h
    _ = (2*2^2)^m := by rw [Nat.mul_pow, Nat.pow_mul]
    _ ≤ (3^2)^m := Nat.pow_le_pow_left (by decide) m
    _ = 3^(2*m) := (Nat.pow_mul ..).symm

/-- A monotone counting function whose aligned blocks obey the digit-sieve
    bound has density zero.  The conclusion is the reciprocal-integer form
    of the epsilon definition, so no real-number library is required. -/
theorem density_of_blocks (tally : Nat → Nat) (hz : tally 0 = 0)
    (mono : ∀ ⦃i j⦄, i ≤ j → tally i ≤ tally j)
    (block : ∀ k q : Nat,
      tally ((q+1)*(2*3^k)) ≤ tally (q*(2*3^k)) + 2^k) :
    ∀ m : Nat, ∃ start : Nat, ∀ n ≥ start, m * tally n ≤ n := by
  intro m
  let k := 2*m
  let p := 2*3^k
  have hp : 0 < p := Nat.mul_pos (by decide) (Nat.pow_pos (by decide))
  have batches (q : Nat) : tally (q*p) ≤ q * 2^k := by
    induction q with
    | zero => simp [hz]
    | succ q ih =>
      exact Nat.le_trans (block k q) (by rw [Nat.succ_mul q (2^k)]; exact Nat.add_le_add_right ih _)
  refine ⟨p, ?_⟩
  intro n hn
  let q := n/p
  have hrem := Nat.mod_lt n hp
  have hdiv : n % p + q*p = n := by
    rw [Nat.mul_comm q p]
    exact Nat.mod_add_div n p
  have hceil : n ≤ (q+1)*p := by rw [Nat.succ_mul]; omega
  have hq : 1 ≤ q := (Nat.le_div_iff_mul_le hp).mpr (by simpa using hn)
  calc
    m * tally n ≤ m * ((q+1) * 2^k) :=
      Nat.mul_le_mul_left m (Nat.le_trans (mono hceil) (batches _))
    _ = (q+1)*(m*2^k) := by ac_rfl
    _ ≤ (q+1)*3^k := Nat.mul_le_mul_left _ (ratio m)
    _ ≤ (q*2)*3^k := Nat.mul_le_mul_right _ (by omega)
    _ = q*p := Nat.mul_assoc .. 
    _ ≤ n := Nat.div_mul_le_self n p

end Erdos406.Count

namespace Erdos406.Count

/-- Number of exponents n < N for which the full ternary expansion of 2^n omits 2. -/
noncomputable def tally := tallyAux DigitFree

/-- At most 2^k globally admissible exponents in *each* aligned interval of
    length 2·3^k. This bound does not depend on where the interval lies. -/
theorem block (k q : Nat) :
    tally ((q+1)*(2*3^k)) ≤ tally (q*(2*3^k)) + 2^k := by
  have hb := tally_cover DigitFree (q*(2*3^k)) (2*3^k)
    ((candidates k).map (fun s => 2*s)) (cover k q)
  simpa only [tally, Nat.succ_mul, List.length_map, length_candidates] using hb

theorem initial_interval (k : Nat) : tally (2*3^k) ≤ 2^k := by
  simpa [tally] using block k 0

/-- Natural density zero. For every positive reciprocal threshold 1/m,
    the fraction of clean exponents eventually stays below or equal to it. -/
theorem density_zero :
    ∀ m : Nat, ∃ start : Nat, ∀ n ≥ start, m * tally n ≤ n :=
  density_of_blocks tally rfl (fun _ _ h => tally_mono DigitFree h) block

end Erdos406.Count

namespace Erdos406.FirstTwo

-- These numeral expansions let `omega` collect coefficients after distribution.
private theorem two : (2 : Nat) = 1+1 := rfl
private theorem three : (3 : Nat) = 2+1 := rfl

private theorem productIdentity (d u v : Nat) :
    (1 + d * 3 * u) * (1 + d * 3 * v) =
      1 + d * 3 * (u + v + 3 * (d*u*v)) := by
  simp only [three, two, Nat.one_mul, Nat.mul_one, Nat.add_mul, Nat.mul_add,
    Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  omega

private theorem liftedUnit (k : Nat) :
    ∃ t, 4 ^ (3 ^ k) = 1 + (3 ^ k * 3) * (1 + 3*t) := by
  obtain ⟨t, ht⟩ := ErdosLift.exact_lift_normalized k
  exact ⟨t, by simpa only [Nat.pow_mul 2 2, Nat.pow_succ 3 k] using ht⟩

private theorem liftedPower (k m : Nat) :
    ∃ w, (4^(3^k))^m = 1 + (3^k*3)*(m+3*w) := by
  obtain ⟨t, ht⟩ := liftedUnit k
  let d := 3^k
  induction m with
  | zero => exact ⟨0, by simp⟩
  | succ m ih =>
    obtain ⟨w, hw⟩ := ih
    let u := m + 3*w
    let v := 1 + 3*t
    refine ⟨w+t+d*u*v, ?_⟩
    rw [Nat.pow_succ, hw]
    rw [ht]
    change (1+d*3*u)*(1+d*3*v) = 1+d*3*(m+1+3*(w+t+d*u*v))
    rw [productIdentity]
    have hh : u+v+3*(d*u*v) = m+1+3*(w+t+d*u*v) := by
      dsimp [u, v]
      omega
    rw [hh]

/-- After the units digit, the first potentially nonzero ternary digit in
`2^(2*3^k*m)` is at position `k+1` (units = position 0). Its value is `m % 3`. -/
theorem digit_at (k m : Nat) :
    (2 ^ (2 * 3^k * m) / 3^(k+1)) % 3 = m % 3 := by
  obtain ⟨w, hw⟩ := liftedPower k m
  rw [Nat.pow_mul, Nat.pow_mul]
  change ((4^(3^k))^m / 3^(k+1)) % 3 = _
  rw [hw]
  have hp : 1 < 3^(k+1) := by
    have h : 0 < 3^k := Nat.pow_pos (by decide)
    rw [Nat.pow_succ]
    omega
  rw [← Nat.pow_succ, Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt hp]
  omega

/-- All lower digits form the suffix 00…01. -/
theorem low_suffix (k m : Nat) :
    2 ^ (2 * 3^k * m) % 3^(k+1) = 1 := by
  obtain ⟨w, hw⟩ := liftedPower k m
  rw [Nat.pow_mul, Nat.pow_mul]
  change (4^(3^k))^m % 3^(k+1) = _
  rw [hw, ← Nat.pow_succ, Nat.add_mul_mod_self_left]
  apply Nat.mod_eq_of_lt
  have h : 0 < 3^k := Nat.pow_pos (by decide)
  rw [Nat.pow_succ]
  omega

/-- The forbidden digit 2 can first occur arbitrarily far from the units place. -/
theorem first_forbidden (k q : Nat) :
    let n := 2 * 3^k * (3*q+2)
    2^n % 3^(k+1) = 1 ∧ (2^n / 3^(k+1)) % 3 = 2 := by
  refine ⟨low_suffix _ _, ?_⟩
  rw [digit_at]
  omega

set_option exponentiation.threshold 40000 in
/-- A near miss for tests that inspect only the two ends. A Python search
found this exponent; the kernel checks all four claims independently. The
leading and trailing 16 trits are 1000010110110010 and 0001011011101111. -/
theorem two_clean_ends :
    let x := 2 ^ 36638
    3^23116 ≤ x ∧ x < 3^23117 ∧
    (∀ i : Fin 16, x / 3^i.val % 3 < 2 ∧ x / 3^(23101 + i.val) % 3 < 2) ∧
    x / 3^18 % 3 = 2 := by
  decide

end Erdos406.FirstTwo

namespace Erdos406

private theorem stripThrees (x : Nat) (hx : 0 < x) :
    ∃ k u : Nat, x = 3^k*u ∧ u%3 ≠ 0 := by
  induction x using Nat.strongRecOn with
  | ind x ih =>
    by_cases h : x%3 = 0
    · have hpos : 0 < x/3 := by omega
      obtain ⟨k, u, he, hu⟩ := ih (x/3) (Nat.div_lt_self hx (by decide)) hpos
      refine ⟨k+1, u, ?_, hu⟩
      calc
        x = 3*(x/3) := by omega
        _ = 3^(k+1)*u := by rw [he, Nat.pow_succ]; ac_rfl
    · exact ⟨0, x, by simp, h⟩

/-- A clean positive exponent cannot have a clean double. In ternary,
    squaring doubles the first nonzero digit above the units digit. -/
theorem no_clean_double (n : Nat) (hn : 0 < n) (h : DigitFree n) :
    ¬DigitFree (2*n) := by
  intro hdouble
  have he := Count.even_of_free n h
  obtain ⟨k, u, hu, hunit⟩ := stripThrees (n/2) (by omega)
  have hn' : n = 2*3^k*u := he.trans (by rw [hu, Nat.mul_assoc])
  have hd := FirstTwo.digit_at k u
  have hnd := h (k+1)
  rw [hn', hd] at hnd
  have h₂ : 2*n = 2*3^k*(2*u) := by rw [hn']; ac_rfl
  have hd₂ := hdouble (k+1)
  rw [h₂, FirstTwo.digit_at] at hd₂
  omega

end Erdos406

#print axioms Erdos406.Count.block
#print axioms Erdos406.Count.density_zero
#print axioms Erdos406.FirstTwo.first_forbidden
#print axioms Erdos406.no_clean_double
