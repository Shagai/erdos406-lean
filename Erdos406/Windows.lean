import Erdos406.Sieve
import Mathlib.NumberTheory.DiophantineApproximation
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace Erdos406.Windows

/-- A positive multiple of x can lie arbitrarily close to an integer from above.
In the negative-error branch, go almost one full turn before returning. -/
theorem oneSided (x ε : ℝ) (hε : 0 < ε) :
    ∃ (k : ℕ) (j : ℤ), 0 < k ∧ 0 ≤ k*x-j ∧ k*x-j < ε := by
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt (lt_min hε zero_lt_one)
  obtain ⟨k, hk, _, hb⟩ := Real.exists_nat_abs_mul_sub_round_le x (Nat.succ_pos N)
  let j := round (k*x)
  have hsmall : |(k:ℝ)*x - j| < min ε 1 := lt_of_le_of_lt hb (by
    exact lt_of_le_of_lt (by gcongr; norm_num) hN)
  by_cases hdir : 0 ≤ (k:ℝ)*x - j
  · exact ⟨k, j, hk, hdir, (abs_of_nonneg hdir ▸ hsmall).trans_le (min_le_left _ _)⟩
  let d : ℝ := j - k*x
  have hd : 0 < d := by dsimp [d]; linarith
  have hds : d < min ε 1 := by
    dsimp [d]
    simpa only [abs_of_neg (lt_of_not_ge hdir), neg_sub] using hsmall
  let t : ℕ := ⌊1/d⌋₊
  have htpos : 0 < t := Nat.floor_pos.mpr ((le_div_iff₀ hd).mpr (by
    simpa using (hds.trans_le (min_le_right _ _)).le))
  have htlo : t * d ≤ 1 := (le_div_iff₀ hd).mp (Nat.floor_le (by positivity))
  have hthi : 1 < ((t : ℝ) + 1)*d := (div_lt_iff hd).mp (Nat.lt_floor_add_one _)
  have he : ((t*k : ℕ):ℝ)*x - ((t*j-1:ℤ):ℝ) = 1-(t:ℝ)*d := by
    dsimp [d]
    push_cast
    ring
  refine ⟨t*k, t*j-1, Nat.mul_pos htpos hk, ?_, ?_⟩
  · rw [he]; linarith
  · rw [he]
    nlinarith [hds.trans_le (min_le_left _ _)]

/-- Move a small positive step just far enough to cross an integer. -/
private theorem shiftedOneSided (x y ε : ℝ) (hε : 0 < ε)
    (hx : ∀ (k : ℕ) (j : ℤ), 0 < k → (k:ℝ)*x ≠ j) :
    ∃ (k : ℕ) (j : ℤ), 0 ≤ y+k*x-j ∧ y+k*x-j < ε := by
  obtain ⟨a,b,ha,hn,hl⟩ := oneSided x ε hε
  let d := (a:ℝ)*x-b
  have hd : 0 < d := lt_of_le_of_ne hn (Ne.symm (sub_ne_zero.mpr (hx a b ha)))
  let J := ⌈y⌉
  let s := (J:ℝ)-y
  have hs : 0 ≤ s := sub_nonneg.mpr (Int.le_ceil _)
  let c := ⌈s/d⌉₊
  have hlo : s ≤ (c:ℝ)*d := (div_le_iff₀ hd).mp (Nat.le_ceil _)
  have hhi : (c:ℝ)*d < s+d := by
    have hh := mul_lt_mul_of_pos_right (Nat.ceil_lt_add_one (div_nonneg hs hd.le)) hd
    rwa [add_mul, div_mul_cancel₀ _ hd.ne', one_mul] at hh
  have he : y+((c*a:ℕ):ℝ)*x-((J+c*b:ℤ):ℝ) = (c:ℝ)*d-s := by
    dsimp [d,s]; push_cast; ring
  exact ⟨c*a,J+c*b,he ▸ sub_nonneg.mpr hlo,he ▸ (by dsimp [d] at *; linarith)⟩

private theorem logTwoNotIntegral {s : ℕ} (hs : 0 < s) (j : ℤ) :
    Real.logb 3 ((2:ℝ)^s) ≠ j := by
  intro he
  have hp := Real.logb_nonneg (by norm_num : (1:ℝ)<3)
    (one_le_pow_of_one_le (by norm_num : (1:ℝ) ≤ 2) s)
  rw [he] at hp
  have hj : 0 ≤ j := by exact_mod_cast hp
  have hm : (j.toNat:ℝ) = j := by exact_mod_cast Int.toNat_of_nonneg hj
  have he' := Real.rpow_logb (by norm_num : 0<(3:ℝ)) (by norm_num : (3:ℝ) ≠ 1)
    (by positivity : 0<(2:ℝ)^s)
  rw [he, ← hm, Real.rpow_natCast] at he'
  have hnat : (3:ℕ)^j.toNat = 2^s := by exact_mod_cast he'
  have hpar := congrArg (fun z : ℕ => z % 2) hnat
  simp [Nat.pow_mod, hs.ne'] at hpar

/-- Every exponent progression has arbitrarily large powers of two just
above a power of three. The multiplicative tolerance is arbitrary. -/
theorem nearOnProgression (P r N : ℕ) (hP : 0 < P) (C : ℝ) (hC : 1 < C) :
    ∃ n m : ℕ, N ≤ n ∧ (∃ u, n = r+P*u) ∧ (3:ℝ)^m ≤ 2^n ∧ (2:ℝ)^n < 3^m*C := by
  let R := r + P*N
  let x := (P:ℝ)*Real.logb 3 2
  let y := (R:ℝ)*Real.logb 3 2
  let ε := min 1 (Real.logb 3 C)
  have epos : 0 < ε := lt_min zero_lt_one (Real.logb_pos (by norm_num) hC)
  have hx (k:ℕ) (j:ℤ) (hk : 0 < k) : (k:ℝ)*x ≠ j := by
    have he : (k:ℝ)*x = Real.logb 3 ((2:ℝ)^(k*P)) := by
      rw [Real.logb_pow (by norm_num : 0 < (2:ℝ))]
      dsimp [x]; push_cast; ring
    exact he ▸ logTwoNotIntegral (Nat.mul_pos hk hP) j
  obtain ⟨k, j, hlo, hhi⟩ := shiftedOneSided x y ε epos hx
  let n := R+P*k
  have hn : y+(k:ℝ)*x = Real.logb 3 ((2:ℝ)^n) := by
    rw [Real.logb_pow (by norm_num : 0 < (2:ℝ))]
    dsimp [n,x,y]; push_cast; ring
  rw [hn] at hlo hhi
  have hlg : 0 ≤ Real.logb 3 ((2:ℝ)^n) := Real.logb_nonneg (by norm_num) (one_le_pow_of_one_le (by norm_num) _)
  have hj : 0 ≤ j := by
    by_contra! hn
    have hj' : (j:ℝ) ≤ -1 := by exact_mod_cast (show j ≤ -1 by omega)
    have h := hhi.trans_le (min_le_left _ _)
    linarith
  let m := j.toNat
  have hm : (m:ℝ) = j := by dsimp [m]; exact_mod_cast Int.toNat_of_nonneg hj
  have hp : 0 < (2:ℝ)^n := by positivity
  have hz : ∀ m : ℕ, Real.logb 3 ((3:ℝ)^m) = m := by
    intro z
    rw [Real.logb_pow (by norm_num), Real.logb_self_eq_one (by norm_num), mul_one]
  refine ⟨n, m, ?_, ?_, ?_, ?_⟩
  · have h' : N ≤ P*N := by simpa using Nat.mul_le_mul_right N (show 1 ≤ P from hP)
    dsimp [n,R]; omega
  · exact ⟨N+k, by dsimp [n,R]; ring⟩
  · apply (Real.logb_le_logb (by norm_num : (1:ℝ)<3) (by positivity) hp).mp
    rw [hz, hm]; linarith
  · apply (Real.logb_lt_logb_iff (by norm_num : (1:ℝ)<3) hp (by positivity)).mp
    rw [Real.logb_mul (by positivity) (by linarith), hz, hm]
    linarith [hhi.trans_le (min_le_right _ _)]

/-- For each width and threshold there is a power of two beginning with
one and w zeroes, ending with w zeroes and one, and having a forbidden
two immediately to the left of the trailing block. -/
theorem arbitraryWindowsWithHiddenTwo (w N : ℕ) : ∃ n m : ℕ, N ≤ n ∧
    w ≤ m ∧ 3^m ≤ 2^n ∧ 3^w*2^n < (3^w+1)*3^m ∧
    2^n % 3^(w+1) = 1 ∧ (2^n / 3^(w+1)) % 3 = 2 := by
  let C : ℝ := 1 + 1/3^w
  have hC : 1 < C := by dsimp [C]; apply lt_add_of_pos_right; positivity
  obtain ⟨n,m,hn,⟨k,hk⟩,hl,hu⟩ := nearOnProgression (2*3^(w+1)) (4*3^w) (max N (3^w)) (by positivity) C hC
  have hub : 3^w*2^n < (3^w+1)*3^m := by
    have h' := mul_lt_mul_of_pos_left hu (by positivity : (0:ℝ)<3^w)
    have he : (3:ℝ)^w * (3^m*C) = (3^w+1)*3^m := by
      dsimp [C]
      field_simp
      ring
    rw [he] at h'
    exact_mod_cast h'
  have hmw : w ≤ m := by
    by_contra! hlt
    have hpow : 3^m ≤ 3^w := Nat.pow_le_pow_right (by decide) hlt.le
    have hbad : 3^w*2^n < 3^w*(3^w+1) := by
      rw [Nat.mul_comm (3^w) (3^w+1)]
      exact hub.trans_le (Nat.mul_le_mul_left _ hpow)
    have hsmall := Nat.lt_of_mul_lt_mul_left hbad
    have hbig := (le_max_right N (3^w)).trans hn
    have := Nat.lt_two_pow n
    omega
  refine ⟨n,m,(le_max_left _ _).trans hn,hmw,by exact_mod_cast hl,hub,?_⟩

  · have hn' : n = 2*3^w*(3*k+2) := by rw [hk, pow_succ]; ring
    rw [hn']
    exact Erdos406.FirstTwo.first_forbidden w k

set_option exponentiation.threshold 310 in
/-- The first three trits of 2^306 are 100; the last four are 2001.
    There are 194 trits in its ternary expansion. -/
theorem example_306 :
    (2:ℕ)^306 / 3^191 = 9 ∧ (2:ℕ)^306 % 81 = 55 := by decide

#print axioms arbitraryWindowsWithHiddenTwo
end Erdos406.Windows
