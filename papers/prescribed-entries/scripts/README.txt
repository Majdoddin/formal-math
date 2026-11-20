Ancillary files of the paper "Prescribed entries of thin matrix products via the laser method" (Ruhollah Majdoddin).

Every certified number of the paper is listed in its Table 9 with the script that certifies it and the lines of the
script's output that print it. Each script's recorded output is beside it, NAME_out.txt; a rerun from this folder on
19 November 2026 reproduced every one of them (lines that report running times aside). The modules r105_v1.py,
r112_smallt.py, r20_rates.py, r32_column_rates.py, r59p2_typical.py, r76_curve.py, r78_decompose.py, r78_family.py are
imported by the scripts below and are not run on their own. The script r211b_cross.py is named in the paper's text,
not in its table; its output is included too.

Run from inside this folder: python3 NAME.py > NAME_out.txt. Order: r79_certify.py writes r79_certify.json, which
r79b_certify.py and r79_curve.py read; r79b_certify.py writes r79b_certify.json, which r79b_curve.py,
r215_a_certify.py and r215_bcd_checks.py read. r109_dual.py reads r78_family_out.txt (the output of r78_family.py,
included), r117_certify.py reads r117_certify_points.txt, and r79_certify.py, r79b_certify.py and r79_curve.py read
r76_lamtable.json (included). Tested with Python 3.13, numpy 2.3, scipy 1.16 and mpmath 1.3.0. Times are wall-clock
times of one run on a desktop computer with four cores (eight threads).

Kind of arithmetic, as in the paper: F exact Fraction arithmetic of Python with enclosed logarithms; M interval
arithmetic of mpmath; D Python's decimal module with directed rounding.

file                               kind needs          time    supports (output lines)
---------------------------------- ---- -------------- ------- --------------------------------------------------
r109_dual.py                       F    numpy          15 s    Theorem 7.4, Corollary 7.5, Corollary 8.4 (lines 31-36)
r117_certify.py                    F    numpy, scipy   1 s     Section 7.4, after Remark 7.17
r211a_excess_certify.py            F    --             1 s     Remark 6.3 (lines 1-3)
r211a_p0_certify.py                F    --             1 s     Lemma 4.14, Corollary 6.2 (lines 1-15)
r211b_cert.py                      F    mpmath         14 s    Section 7.4, after Remark 7.17 (lines 125-140); Theorem 7.4,
                                                              Corollary 7.5, Corollary 8.4 (lines 14-30); Theorem 7.8 (lines
                                                              41-84)
r211b_curve.py                     F    numpy, scipy   39 s    Theorem 7.15 (lines 1-2, 23-43); Theorem 7.15, Remark 6.3 (lines
                                                              45-49)
r211b_lib.py                       F    mpmath         ?       Theorem 7.4, Corollary 7.5, Corollary 8.4
r211c_cert.py                      F,M  numpy, scipy   8 s     Lemma 4.14 (lines 7); Lemma 4.14, Corollary 6.2 (lines 1-8); Lemma
                                                              8.2 (lines 10-24); Theorem 8.3 (lines 26-45)
r211d_checks.py                    F    --             20 s    Section 9.4 (instance of Proposition 9.12) (lines 6)
r211e_cert.py                      F    numpy, scipy   17 s    Lemma 5.1, Theorems 5.2, 5.7, 5.13, Proposition 5.4 (lines 10-33);
                                                              Remark 5.6 (lines 6-8)
r211e_cert2.py                     F    scipy          6 s     Lemma 5.1, Theorems 5.2, 5.7, 5.13, Proposition 5.4 (lines 4-14)
r211f_certify.py                   F    --             3 s     Lemma 10.10, Theorem 10.11 (lines 4-26); Lemma 4.14, Corollary 6.2
                                                              (lines 28-30); Proposition 10.20 (lines 50-61); Remark 10.19
                                                              (lines 41-48, 63-73)
r215_a_certify.py                  F    --             1 s     Corollary 6.13, Proposition 10.16 (lines 1-72)
r215_bcd_checks.py                 F    --             1 s     Corollary 5.9 (lines 31); Proposition 10.20 (lines 1-26)
r217b_e15_table.py                 F    --             1 s     Proposition 10.20 (lines 15); Remark 10.19 (lines 1-14)
r217d_checks.py                    F,F, D --             1 s     Lemma 9.30, Remark 9.33, Example 9.28 (lines 1-37); Section 9.4
                                                              (instance of Proposition 9.12) (lines 19-21)
r220e_checks.py                    F    --             1 s     Proposition 11.15 (lines 70-71)
r74a_certify.py                    F    numpy, scipy, mpmath 80 s    Theorem 7.4, Corollary 7.5, Corollary 8.4 (lines 17-40)
r79_certify.py                     F,M  numpy, mpmath  61 s    Lemma 4.14, Corollary 6.2 (lines 1-4); Lemma 8.2 (lines 6-30)
r79_curve.py                       M    mpmath         1 s     Corollary 8.4 (lines 46-53); Corollary 8.8 (lines 43-44); Theorem
                                                              8.3 (lines 12-40)
r79b_certify.py                    M    numpy, mpmath  3 min   Lemma 4.14 (lines 3); Lemma 8.2 (lines 5-83)
r79b_curve.py                      M    --             2 s     Theorem 8.3 (lines 3-144)
