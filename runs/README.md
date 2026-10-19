# Output logs of the computations in Section 10

Each `.out`/`.txt` file is the unedited standard output of one run. `PAL` lines are palindromes found; `DONE`/`BASE`
lines are end-of-run summaries (steps, candidates checked exactly, palindromes found).

| file | result | command (see `../code/README.md`) |
|---|---|---|
| `r5_1000_p0.out`, `r5_1000_p1.out` | (C1): all n ≤ 1000, all bases 3 ≤ b ≤ 2^β(n) − 1, with positive control | `minbase5 range 1000 {0,1} 2 plus1` |
| `sq_32_p*.out` … `sq_39_p*.out` | (C2): n = a², 32 ≤ a ≤ 39, all bases b < 2^a − 1 | `minbase5 single a² 2^a−1 {0,1} 2` |
| `pc400.out`, `pc784_p*.out` | positive controls for `single` mode (n = 400, 784) | `minbase5 single 400 1048576 0 1`, `minbase5 single 784 268435456 {0,1} 2` |
| `fb_b3_1e10.txt` | (C3): base 3, n ≤ 10^10 | `fixbase 3 3 10000000000 alpha.txt` |
| `fb_1000_1e6.txt` | (C4): 3 ≤ b ≤ 1000, n ≤ 10^6 | `fixbase 3 1000 1000000 alpha.txt` |
| `fb_65536_1e5.txt.gz` | (C4): 1000 < b < 2^16, n ≤ 10^5 (gunzip before use) | `fixbase 1001 65535 100000 alpha.txt` |
| `u4_140_p0.out`, `u4_140_p1.out` | (C5): all representations with ≥ 5 digits, n ≤ 140 | `minbase5 upto4 140 {0,1} 2 root4.txt` |
| `three_out.txt` | Section 8: number of non-binomial (1,c,1)_b representations for each n ≤ 110, with up to three bases | `python3 three.py` |
| `beta_ties.txt` | near-ties in the floating-point β table (only n = 6, x = 2), resolved exactly | `betacalc` |

The n ≤ 60 enumeration of (C5) is `../code/allpal_60.txt`.
