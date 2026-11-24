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
