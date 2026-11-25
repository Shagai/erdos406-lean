# What the first and last digits can tell us about Erdős problem 406

Are there only finitely many exponents n for which the base-three expansion of 2ⁿ omits the digit 2? The known exponents are 0, 2, and 8. This project proves partial results and leaves the finiteness conjecture open.

## Origin of this experiment

Jorge Camarero Vera asked ChatGPT/Codex to choose a random open Erdős problem and attempt a proof or disproof in Lean. Codex selected the problem from a shortlist, searched the literature, developed the proof arguments, wrote the Lean code, and ran the build. The proof sources and pinned dependencies are included so readers can check the statements and reproduce the experiment.

The example that motivated the title is $2^{306}$. In base three it starts with `100` and ends with `2001`. Inspect only the first and last three digits and you miss the 2 immediately before the suffix. The same construction works for every fixed width, however large.

## What Lean checks

- **Density zero.** In each aligned interval [q·2·3ᵏ, (q+1)·2·3ᵏ), at most 2ᵏ exponents can qualify. If T(N) counts all qualifying exponents below N, then for every positive m there is a threshold after which mT(N) ≤ N. See `Erdos406.Count.block` and `Erdos406.Count.density_zero`.
- **Arbitrarily long misleading digit windows.** For every positive width L and every exponent cutoff, there is a power above the cutoff that begins with a 1 followed by L−1 zeros and ends with L−1 zeros followed by a 1. The next digit immediately to the left of that suffix is 2. For example, 2³⁰⁶ has 194 ternary digits, begins with 100, and ends with 2001. See `Erdos406.Windows.arbitraryWindowsWithHiddenTwo` (its parameter w equals L−1) and `example_306`.
- **A finite certificate.** For 0 ≤ n ≤ 10,000, the qualifying exponents are exactly 0, 2, and 8. Checking the lowest 22 digits catches every other exponent in this interval, and 2¹¹³⁴ needs all 22. See `Erdos406.digitFree_iff_of_le_10000` and `first_two_at_21`.
- **Doubling an exponent.** For n > 0, if 2ⁿ omits 2, then 2²ⁿ has a ternary digit 2. See `Erdos406.no_clean_double`.

## The proof attempt

Every qualifying exponent is even, so write it as 2s. Increasing s by 3ᵏ preserves the last k+1 digits of 4ˢ and increases the next digit by one modulo 3. Of the three possible lifts of a residue class, two pass the next digit test. Starting with the units digit 1 gives the aligned interval bound. The bound grows with k and leaves room for infinitely many qualifying exponents.

For the test at both ends, choose exponents of the form n = 4·3ʷ + 2·3ʷ⁺¹·t. A congruence forces the last w+1 digits to be the zero-padded integer 1 and the preceding digit to be 2. Within this same progression, one-sided approximation of n·log₃2 by an integer m puts 2ⁿ between 3ᵐ and (1+3⁻ʷ)·3ᵐ, as far out as needed. These inequalities give the desired leading digits.

## Reproduce

The project pins Lean 4.12.0 and mathlib v4.12.0. With elan installed, run the following commands in the directory containing this README. The first command retrieves precompiled mathlib dependencies.

```sh
lake exe cache get
lake build
```

The modules print the axioms of their principal theorems. The reported dependencies are drawn from Lean's standard `propext`, `Classical.choice`, and `Quot.sound`. Finite arithmetic certificates use the kernel-reduced `decide` tactic.

## Literature

The density-zero conclusion is classical. Narkiewicz proved an upper bound of order N^(log₃2). Saye verified a much larger finite interval, through exponent 2·3⁴⁵. Yagub Aliyev's 2023 paper gives closely related results. Lemma 3.3 and its proof identify periodic exponent classes realizing each admissible suffix. Lemma 4.1 uses the density of the fractional parts of $n\log_3 2$ to prescribe leading digits. On an exponent progression $n=r+Pt$ with positive period $P$, the step $P\log_3 2$ is still irrational. Applying the prefix argument on that progression gives the simultaneous choice used here. The contribution of this repository is a reproducible Lean formalization and worked example.

- [Erdős, Some Unconventional Problems in Number Theory, 1979, p. 67](https://www.renyi.hu/~p_erdos/1979-22.pdf)
- [Bloom, Erdős Problem 406](https://www.erdosproblems.com/406)
- [Lagarias, Ternary Expansions of Powers of 2, 2009, including Narkiewicz's bound](https://doi.org/10.1112/jlms/jdn080)
- [Saye, On Two Conjectures Concerning the Ternary Digits of Powers of Two, 2022](https://cs.uwaterloo.ca/journals/JIS/VOL25/Saye/saye3.html)
- [Aliyev, Digits of powers of 2 in ternary numeral system, 2023, Lemmas 3.3 and 4.1](https://nntdm.net/papers/nntdm-29/NNTDM-29-3-474-485.pdf)
