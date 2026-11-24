# qg-d2 (session_01GmnDhgAdyDijthBgZgJFWn): a uniform certificate for the F2 step (13:11 UTC; owner: "make the circuits generalize to size n")
Goal: an explicit, size-independent certificate behind the F2 step (DECISION 12:46: some alive v has |F2(Q) \ F2(Q+v)| >= cost(v)),
so that the proof for all n is a proof of the certificate. Code: 951/tools/kill_tests/ucert.py (imports w951); per-instance data
951/data/ucert/ucert_corpus.jsonl.gz. Corpus: data-corpora + front's w7/w8/w8b/chk/w9 + 951/data/witnesses, deduplicated: 46,078
correct one-NOT circuits (n <= 9), Q = {} plus 3 random sparse Q each: 102,137 instances; 31,503 with every gate read.
CERTIFICATE CERT-1c: for each alive w through v, the CONE merge set M^cone_Q(w) = Lemma-M union-find at the zero point Z = Q run only
over the gates in the cone of o_w. Each has exactly d_w gates (0 exceptions in 102,137 instances), so if those of the sets through v
are pairwise disjoint and all leave F2 under x_v := 1, gain(v) >= cost(v) with an explicit injection.
- CHECKED: CERT-1c holds at some alive v on ALL 31,503 instances with every gate read (a MinCE has every gate live, R4), and on
  102,136 / 102,137 overall; the one failure is the junk barrier pappus_junk_gain (Q = 9, unread gates). With a per-set choice of
  zero point Z_w ⊇ Q instead of Z = Q (H3c): 102,137 / 102,137. Without the cone restriction: 15 failures (junk gates outside the
  cone win the union-find, star4, cx44_1_junk); top_w instead of Q (H2c): 971 failures.
- Every alive v works on 30,916 / 31,503 (98.1%). Failing (instance, v) pairs: 558 because a merge gate survives x_v := 1, 121
  because two merge sets overlap, 0 both. Smallest: death ess_k4e_clean.jsonl:1567 (n = 4, Q = {}, v = 1); overlap chk/k.jsonl:1929
  (n = 4, Q = {}, v = 0).
- No simple v-rule: some max-degree v fails 24 times (smallest w7/bad.jsonl:125, n = 5), every heavy v 125, some min-degree v 11.
  Averaging over v does not give it either: sum_v gain >= sum_v cost fails on 3 (w7/bad.jsonl:148, :151, both every gate read),
  weights 1/deg, 1/deg^2, 1/cost, light x2 fail on 31-34.
PROOF PLAN this suggests (OPEN): two size-independent lemmas about cone merge sets at the bottom point Q, for a well-chosen v:
  (D) death: no gate of M^cone_Q(w), w ∋ v, has a witness Z' ⊇ Q + v (by Lemma D: none of its witnesses at Q contains v);
  (S) disjointness: the cone merge sets at Q of the sunflower of sets through v are pairwise disjoint.
  The v choice must avoid the two failure kinds above; the data says almost any v works, none of the simple rules always does.
- LEAN (cTAHG, 13:24 UTC): the reduction (D) ∧ (S) at v ⇒ GainF2 at v is CHECKED, ConeCert.lean `gainF2_of_cert` / `gainF2_of_cert1c`
  (`CertD`, `CertS` as hypotheses; `coneMerge` = Lemma M over the masked cone), plugged into `no_minCE_of_cert_or_local`.

## Lemma (D) (qg-d2 took (D); cTAHG has (S); 13:44 UTC). Code: 951/tools/kill_tests/certd.py. Lean: 951/lean/PEqualNP/W951/CertDHeavy.lean
Instances: every gate read and the NOT gate not a literal or constant on the cube x_Q = 1 (not CubeLocal): 17,045 instances, 70,299 (instance, v).
- (D) at z = Q holds at 69,842 / 70,299 v (99.35%) and at some v in EVERY instance; with a per-set zero point (CERT-3c) at 70,112 v.
- Survivors (470 cone merge gates at z = Q that stay in F2 under x_v := 1): 447 are NOT 1 at Q + e_v, i.e. merges between two points of S_w
  other than v; the 23 that are 1 at Q + e_v all have a light v (F1* survivors: world-0 witness, NOT-dependent). At a heavy v: 0 survivors 1 at Q + e_v.
- LEAN (PROVED, propext / Classical.choice / Quot.sound): certD_of_heavy_see — at a HEAVY v (NOT gate 0 at Q + e_v), if every cone merge of
  every set through v is 1 at Q + e_v (SEE; automatic for 2-sets), then (D) holds, for any zero points. Proof: F1 (F1_real_zero).
  Checks per 951/README.md: full build 1 sorry outside PayDraft (no_minCE), one-file 0 errors / 1 sorry, L_meta_951 axioms as required.
- DATA for that route: heavy v with SEE exists in 12,620 / 12,853 instances that have a heavy point; (D) then holds 25,081 / 25,081.
  OPEN for (D): (a) the 233 instances with heavy points but no heavy SEE point (smallest ess_rand_clean.jsonl:1378, n = 5); (b) the 4,192
  instances with no heavy point (the light case; F1* bounds the survivors that see v). The v must also satisfy (S).

## PROVED COVERAGE (13:46 UTC; cTAHG's (S) = certS_of_tu, TUCert.lean d63060f + qg-d2's (D) = certD_of_heavy_see). Code: 951/tools/kill_tests/proved_cover.py
Same 17,045 non-local, every-gate-read instances (circuit, Q). An instance is COVERED when some alive v is heavy and the sets through v
have zero points z_w ⊇ Q off S_w that are pairwise TU in one direction (so (S) by certS_of_tu) and whose cone merges are all 1 at
Q + e_v (so (D) by certD_of_heavy_see, no data). Then CERT-3c, hence the F2 step at that instance, follows from proved lemmas only.
- COVERED: 12,604 / 17,045 (73.9%); among instances with a heavy point 12,604 / 12,853 (98.1%).
- cTAHG's checker (tu_cert.instance, unchanged) on the same set: CERT-1c observed 17,045 / 17,045; H3u (TU + (D) observed) 17,035 /
  17,045 (the 10 misses are fixh16, h = (x0|x1)(x2|x3)); at points of degree >= 2, TU never holds with all z_w = Q, so (D) is always
  needed at higher zero points there (H3u at 50,851 / 57,209 such (instance, v)).
- OPEN, exactly: (H') 249 heavy instances not covered (smallest w7/bad.jsonl:137, n = 5, s = 9, Q = 16); (L) the 4,192 instances with
  no heavy point, where (D) needs F1* (survivors that see v are world-0, NOT-dependent) instead of F1.

## UNIFIED (D) (13:48 UTC): certD_of_see0 (Lean, W951/CertDHeavy.lean; propext / Classical.choice / Quot.sound)
(D) at ANY v, heavy or light, when every cone merge of every set through v is 1 at Q + e_v in the real circuit AND in C_0 (NOT gate
forced to 0): by F1* (F1star_mem), a gate of F2(Q ∪ {v}) that is 1 at Q + e_v has C_0 = 0 there. At a heavy v real = C_0, so this
contains certD_of_heavy_see.
PROVED COVERAGE with cTAHG's certS_of_tu (proved_cover.py, flag proved0): 16,970 / 17,045 non-local every-gate-read instances
(99.56%): light 4,170 / 4,192, heavy 12,800 / 12,853. OPEN: 75 instances; smallest fixh16_clean.jsonl:1192 (n = 4, s = 16, light,
h = (x0|x1)(x2|x3), the family where cTAHG's TU check also misses). Checks per 951/README.md re-run on main 8764bae + this.
