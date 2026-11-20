Ancillary files of arXiv:2610.17420, second version (Ruhollah Majdoddin).

This folder holds the files of the first version, unchanged except for one sentence in the docstring of
exact_ceiling.py, and the files added in the second version, whose names (r and a number) are those of the author's
research record. Each added script has its recorded output beside it, NAME_out.txt; a rerun from this folder on 19
November 2026 reproduced every one of them (lines that report running times aside). The added modules r150d_rates.py,
r155_cert.py, r155_lib.py, r155_rates.py, r206a_iv.py, r206j_iv.py are imported by the scripts named in the table and
are not run on their own.

Run each script from inside this folder: python3 FILE [MODE], and for an added script python3 FILE > FILE_out.txt to
compare. Tested with Python 3.13, numpy 2.3, scipy 1.16, sympy 1.14 (identity_check.py only) and mpmath 1.3.0 (the
scripts whose needs say mpmath). Times are wall-clock times of one run on a desktop computer with four cores (eight
threads).

Kind:  P = re-checks a statement that is proved in the paper;
       C = part of a computer-assisted proof (a certificate in exact rational or interval arithmetic);
       N = computes a numerical value or heuristic evidence that is not proved.
Statement numbers are those of the second version.

file [mode]                        kind needs          time    supports
---------------------------------- ---- -------------- ------- --------------------------------------------------
identity_check.py                  P    sympy          1 s     Lemma 3.1, Remark 5.2, the two signs of Coppersmith's identity
                                                              (Section 3) illegible in the scan
squared_check.py                   P    numpy          11 s    Theorem 5.1, Lemmas 6.1, 7.1, queries (Remark 12.2)
omv512_check.py                    P    --             1 s     the index identities of Proposition 12.3
example_squared.py                 P    --             37 s    the example of Section 5
explicit_constants.py              P, N numpy, scipy   6 s     Corollary 11.1 (P); Table 5, lines E1, E2 (Table 2), E3 (Remark
                                                              6.2) (N)
koszul_exact.py                    C    --             1 s     Remark A.7
koszul_modp.py base | excl | ctrl  C    numpy          7 s, 1 s, 1 s Remark A.6 (base), Remark A.7 (excl), controls
border_apolarity.py G222 5 | G221 5 | G222 6 C    --             1 s, 1 s, 2 s Proposition 3.2 (G222 5), controls
border_apolarity_family.py S221 5 | S222 5 C    sympy          6 s, 1 s Proposition 3.2, controls
border_rank_probe.py               N    numpy          75 s    the probe after Proposition 3.2
exact_ceiling.py                   N    numpy, scipy   12 s    the exact-count limits 0.1784, 0.1292, Section 10; for the data
                                                              structure with the exact box count the same limit is proved
                                                              (Theorem 8.2)
profile_model.py                   N    numpy          2.5 min the shared model; 0.003935 (Schönhage (3,3))
schoenhage_scores.py               N    --             15 s    Schönhage's family, (3,3) largest
border_identity_scores.py          N    numpy          25 min  the family's scores; open shapes <=0.00573
shared_variable_variants.py        N    numpy          9 min   lines H (0.005825), A (Remark 5.3), K1 (one product per run)
pure_inner_cases.py                N    numpy          16 min  the cases R_0>=2, kn<=30
vrana_patterns.py enum             N    numpy          6 min   Vrana's 464 leaf counts
cw_decompositions.py grouped | robust | wstyle | scan 2 4 8 N    numpy          14 min, 3 min, 42 s, 1 h Coppersmith--Winograd decompositions
thin_exclusion.py                  C    --             1 s     Corollary A.18: the shapes of the 145
thin_region.py                     N    --             10 min  the region of Proposition A.17(iii)
thin_value.py squares | rect | sup N    --             1 s, 6 s, 1 s what open thin shapes could be worth
q2lib.py                           C    numpy          --      lattice tests with certificates, gadget search and orbits for the
                                                              four scripts below
q2_boolean.py                      C    numpy          1 s     Theorem 28.11, Table 12
q2_functional3.py                  C    numpy          38 s    Theorem 28.12, Table 14
q2_latin.py                        C    numpy          27 s    Proposition 28.14(b), (c)
q2_functional4.py functional4 | nonfunctional3 | local4 C, N numpy, cc      31 min, 19 s, 2.7 min Proposition 28.14(e), Table 15 (functional4); Proposition 28.14(f)
                                                              (nonfunctional3); the counts before Open problem 28.16 (local4, N)
enum_functional.c, locrep.c        C, N cc             --      C helpers of q2_functional4.py
r14_witness_check.py               C    mpmath         1 s     the two witnesses of Theorem 8.2 (q < 1/2 and q < 1)
r114a_certify.py                   C    scipy          2 s     the thresholds at q=1 and q=1/2 of Corollary 13.7
r206j_certify.py                   C    --             21 min  the same thresholds, an independent program with its own interval
                                                              logarithms (r206j_iv.py)
r114a_toy_check.py                 P    numpy          11 min  Lemmas 13.3, 13.4 and 13.5 by brute force on small instances
                                                              (Remark 13.11); imports squared_check.py
r206j_brute.py                     P    --             55 s    the same lemmas, an independent brute force
r206a_r110p.py [points]            C    numpy          9 s     the pruned chain of Lemma 14.2 (Table 6); two runs, see README.txt
r110b_certify.py                   C    numpy          1 s     the plain chain of Lemma 14.2
r206c_certify.py                   C    --             1 s     the plain chain again, an independent program; eta=63/18437 of
                                                              Proposition 14.4
r111b_cert.py                      C    --             10 s    the certified points of Corollary 9.4
r206a_cert111b.py                  C    --             2 s     the same points, an independent program (interval logarithms
                                                              r206a_iv.py)
r214_abfk_cert.py                  C    --             1 s     the values of F and (kappa+1)F(kappa)<1 in Corollary 15.2
r206d_check.py                     P    --             1 s     Corollary 15.2, independent numerical checks (reads
                                                              r79b_certify.json)
r206b_check.py                     P    --             4 s     Theorem 22.4: its lemma on common bit lengths exhaustively and its
                                                              algorithm on small instances
r61b_range.py                      C    numpy, scipy   2 min   the constants and thresholds of Corollary 17.3
r201_cor5_check.py                 P    --             14 s    Corollary 17.3, an independent program
r61b_certify.py                    C    mpmath         6 s     the certificate of Theorem 17.5 (weak duality and a tangent plane)
r154b_certify.py                   C    mpmath         3 min   the same certificate by a second method (a separable Lagrange
                                                              bound)
r61b_certify2.py                   C    mpmath         1 s     the certificate of Theorem 17.4 (a tangent plane)
r202_thm7_certify.py               C    mpmath         1 s     the same certificate by a Lagrange dual
r155_fold.py                       C    numpy, scipy   49 s    Table 11, the folded points of Theorem 23.3 (with r155_cert.py,
                                                              r155_lib.py, r155_rates.py, r150d_rates.py)
r224_unfold_check.py               C    numpy, scipy   2 s     the same points checked unfolded: H_2 at 1/eps=1/e_0+1/4 by the
                                                              inequalities of r155_cert.py
r154c_cert.py                      C    mpmath         2 s     Table 11 by a second method (reads r154c_certdata.json,
                                                              r154c_certdata_full.json)

Commands and what to look for:

    python3 identity_check.py               # checks 1-5 print OK
    python3 squared_check.py                # 0 wrong outputs at 2+2, 3+3, 4+4 levels; the control without the
                                            # split by s fails; every query right
    python3 omv512_check.py                 # both identities hold on 3000 random Boolean instances
    python3 example_squared.py              # the numbers of the example; 0 wrong of 2304 read output strings
    python3 explicit_constants.py           # needs scipy; constants of Corollary 11.1, the rate table,
                                            # lines E1, E2, E3
    python3 koszul_exact.py                 # S(2,2,2) >= 6, S(2,3,3) >= 8, S(2,3,4) >= 9, S(2,3,5) >= 10,
                                            # S(2,2,3) >= 7; controls S(2,2,1) 5, S(2,3,2) 7
    python3 koszul_modp.py base             # S(1,n,q0') >= n+q0'+1 for n = 2, q0' <= 6 and q0' = 1, n <= 6
    python3 koszul_modp.py excl             # the four bounds of Remark A.7
    python3 koszul_modp.py ctrl             # controls
    python3 border_rank_probe.py            # G(2,2,2) stops at residual 1.0 from every start, like the
                                            # infeasible controls; the feasible controls approach 0
    python3 exact_ceiling.py                # needs scipy; "eps at c_min, gamma=0": 0.17843 (squared),
                                            # 0.12923 (Schoenhage)
    python3 profile_model.py                # Schoenhage (3,3): eps*gamma = 0.003935
    python3 schoenhage_scores.py            # (3,3) largest, 0.003935
    python3 border_identity_scores.py       # 0.005825 (2,2); 0.005489 (2,3); 0.004771 (3,3); 0.004720 (2,4);
                                            # open shapes 0.005730, 0.004667
    python3 shared_variable_variants.py     # lines H, A, K1
    python3 pure_inner_cases.py             # 69 cases; every case with R0 >= 2 prints "no saving"
    python3 vrana_patterns.py enum          # 464 distinct class profiles, none with a saving
    python3 cw_decompositions.py grouped    # every min Gamma/m is positive
    python3 cw_decompositions.py robust     # every value >= 0
    python3 cw_decompositions.py wstyle     # +0.3812, +0.7278, +1.0744, +1.4210
    python3 cw_decompositions.py scan 2 4 8 # 126 profiles, none negative
    python3 thin_exclusion.py               # (a) not excluded: none; (c) none; exit status 0
    python3 thin_region.py                  # b=2: 23 34 [(34, 2, 35), ...]; b=3: 31 46; b=4: 38 58; ...
    python3 thin_value.py                   # squares: b 2 first k ... 51; rect: b 2 ... o1=42; sup: overall 0.07332
    python3 q2_boolean.py                   # 22 orbits; "relations with REP and t=1 gadget: 0 ; with neither: 0"
    python3 q2_functional3.py               # 84 orbits; non-constant classification: 0; "0 third-class orbits"
    python3 q2_latin.py                     # order 4: 2 orbits, sizes [144, 432]; L5 REP False, gadget False
    python3 q2_functional4.py               # line A: Burnside 167342 = enumerated; line B: 167342 of 167342
                                            # agree; line C: {'REP': 42, 'gadget': 167296, 'neither': 4};
                                            # line E: 0; line I: the 4 third-class orbits, 15552 maps
    python3 q2_functional4.py nonfunctional3  # line A: 22100; line B: 0; line D: 1296 relations in 4 orbits
    python3 q2_functional4.py local4        # line B: 186526704; line C: {'not REP': 10979, 'REP': 9021}

The shapes of the 145 decompositions of full products found by computer search (AlphaTensor, the flip graphs of Kauers
and Moosbauer, AlphaEvolve) are listed in thin_exclusion.py; they were read once from the published files named in
Appendix A.1, which are not included. The corollary on the 145 (Appendix A, "Thin full products") needs only the list.

Commands for the files added in the second version:

    python3 r206a_r110p.py 0.0074 0.03188 0.00746 0.03188 > r206a_r110p_out.txt
    python3 r206a_r110p.py --slack=1e-7 0.007467 0.031884 >> r206a_r110p_out.txt
                                            # the two runs of the pruned chain (one output file)
    python3 r206d_check.py > r206d_check_out.txt   # reads r79b_certify.json, written by r79b_certify.py of the
                                            # companion paper's ancillary files and included here as data
    python3 r154c_cert.py > r154c_cert_out.txt     # reads the multipliers r154c_certdata.json and
                                            # r154c_certdata_full.json; last line ALL CERTIFIED
    python3 r224_unfold_check.py > r224_unfold_check_out.txt   # last line ALL CERTIFIED
    python3 NAME.py > NAME_out.txt          # every other added script
