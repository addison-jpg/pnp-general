//! Native recomputation of culture/love: the same definitions as check.py, paths.py and field.py.
//! std only. Build: cargo build --release (put CARGO_TARGET_DIR outside the repository).
//! Modes:
//!   love-native diff   every number of the Python fingerprints this crate covers, n <= 3, as JSON lines
//!   love-native new    (a) the k=1 stable polytope on every n=3 profile, (b) n=4 at k=1 by symmetry reduction
//! Driven by culture/love/native_diff.py, which compares `diff` with the Python fingerprints first.
//! Arithmetic on the polytopes is exact: Q below is an i64 fraction with i128 intermediates; any overflow
//! panics, and the release profile aborts on panic.
use std::collections::{HashMap, VecDeque};
use std::time::Instant;

// ---------------------------------------------------------------- exact rationals
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
struct Q { n: i64, d: i64 } // d > 0, gcd(|n|, d) = 1

fn gcd(mut a: i128, mut b: i128) -> i128 { a = a.abs(); b = b.abs(); while b != 0 { let t = a % b; a = b; b = t; } a }
fn mk(n: i128, d: i128) -> Q {
    assert!(d != 0, "division by zero");
    let g = gcd(n, d).max(1);
    let (mut n, mut d) = (n / g, d / g);
    if d < 0 { n = -n; d = -d; }
    Q { n: i64::try_from(n).expect("fraction overflow"), d: i64::try_from(d).expect("fraction overflow") }
}
fn qi(n: i64) -> Q { Q { n, d: 1 } }
fn add(a: Q, b: Q) -> Q { mk(a.n as i128 * b.d as i128 + b.n as i128 * a.d as i128, a.d as i128 * b.d as i128) }
fn sub(a: Q, b: Q) -> Q { add(a, Q { n: a_neg(b.n), d: b.d }) }
fn a_neg(x: i64) -> i64 { x.checked_neg().expect("fraction overflow") }
fn mul(a: Q, b: Q) -> Q { mk(a.n as i128 * b.n as i128, a.d as i128 * b.d as i128) }
fn div(a: Q, b: Q) -> Q { mk(a.n as i128 * b.d as i128, a.d as i128 * b.n as i128) }
fn sign(a: Q) -> i32 { a.n.signum() as i32 }

// ---------------------------------------------------------------- the integer model (check.py)
fn perms(n: usize) -> Vec<Vec<u8>> {
    // lexicographic, as itertools.permutations(range(n))
    fn rec(n: usize, cur: &mut Vec<u8>, used: &mut Vec<bool>, out: &mut Vec<Vec<u8>>) {
        if cur.len() == n { out.push(cur.clone()); return; }
        for x in 0..n { if !used[x] { used[x] = true; cur.push(x as u8); rec(n, cur, used, out); cur.pop(); used[x] = false; } }
    }
    let mut out = vec![]; rec(n, &mut vec![], &mut vec![false; n], &mut out); out
}

/// every side tuple (one ranking per member), in itertools.product order: row 0 is the most significant digit
fn sides(n: usize, ps: &[Vec<u8>]) -> Vec<Vec<Vec<u8>>> {
    let f = ps.len(); let total = f.pow(n as u32); let mut out = Vec::with_capacity(total);
    for s in 0..total {
        let mut rows = vec![]; let mut x = s;
        let mut digs = vec![0; n]; for a in (0..n).rev() { digs[a] = x % f; x /= f; }
        for a in 0..n { rows.push(ps[digs[a]].clone()); }
        out.push(rows);
    }
    out
}

/// rank[i][j]: position of j in i's list (0 = best)
fn ranks(prefs: &[Vec<u8>]) -> Vec<Vec<u8>> {
    prefs.iter().map(|p| { let mut r = vec![0u8; p.len()]; for (pos, &j) in p.iter().enumerate() { r[j as usize] = pos as u8; } r }).collect()
}

fn matchings(n: usize, k: usize) -> Vec<u16> {
    let mut out = vec![];
    for m in 0u32..(1u32 << (n * n)) {
        let mut da = vec![0; n]; let mut db = vec![0; n];
        for q in 0..n * n { if m >> q & 1 == 1 { da[q / n] += 1; db[q % n] += 1; } }
        if da.iter().chain(db.iter()).all(|&x| x <= k) { out.push(m as u16); }
    }
    out
}

fn partners(n: usize, m: u16, me: usize, side: usize) -> Vec<usize> {
    (0..n).filter(|&o| { let q = if side == 0 { me * n + o } else { o * n + me }; m >> q & 1 == 1 }).collect()
}

fn wants(r: &[Vec<u8>], me: usize, other: usize, ps: &[usize], k: usize) -> bool {
    ps.len() < k || r[me][other] < ps.iter().map(|&p| r[me][p]).max().unwrap()
}

/// one side's "would join" pairs as bits a*n+b (check.side_bits)
fn side_bits(n: usize, k: usize, r: &[Vec<u8>], m: u16, side: usize) -> u16 {
    let mut bits = 0u16;
    for me in 0..n {
        let ps = partners(n, m, me, side);
        for other in 0..n {
            let q = if side == 0 { me * n + other } else { other * n + me };
            if m >> q & 1 == 0 && wants(r, me, other, &ps, k) { bits |= 1 << q; }
        }
    }
    bits
}

/// the bit of the pair `me` drops on a move, 0 with a free place (paths.drop_bits)
fn drop_bits(n: usize, k: usize, r: &[Vec<u8>], m: u16, side: usize) -> Vec<u16> {
    (0..n).map(|me| {
        let ps = partners(n, m, me, side);
        if ps.len() < k { return 0; }
        let w = *ps.iter().max_by_key(|&&o| r[me][o]).unwrap();
        if side == 0 { 1 << (me * n + w) } else { 1 << (w * n + me) }
    }).collect()
}

/// direct pair-by-pair stability, used to check the bit form
fn stable_direct(n: usize, k: usize, ra: &[Vec<u8>], rb: &[Vec<u8>], m: u16) -> bool {
    for a in 0..n { for b in 0..n {
        if m >> (a * n + b) & 1 == 1 { continue; }
        if wants(ra, a, b, &partners(n, m, a, 0), k) && wants(rb, b, a, &partners(n, m, b, 1), k) { return false; }
    } }
    true
}

struct Tables { m: Vec<u16>, r: Vec<Vec<Vec<u8>>>, wa: Vec<Vec<u16>>, wb: Vec<Vec<u16>>, da: Vec<Vec<Vec<u16>>>, db: Vec<Vec<Vec<u16>>> }
fn tables(n: usize, k: usize) -> Tables {
    let ps = perms(n); let sd = sides(n, &ps); let m = matchings(n, k);
    let r: Vec<_> = sd.iter().map(|s| ranks(s)).collect();
    let wa = r.iter().map(|x| m.iter().map(|&mm| side_bits(n, k, x, mm, 0)).collect()).collect();
    let wb = r.iter().map(|x| m.iter().map(|&mm| side_bits(n, k, x, mm, 1)).collect()).collect();
    let da = r.iter().map(|x| m.iter().map(|&mm| drop_bits(n, k, x, mm, 0)).collect()).collect();
    let db = r.iter().map(|x| m.iter().map(|&mm| drop_bits(n, k, x, mm, 1)).collect()).collect();
    Tables { m, r, wa, wb, da, db }
}

#[derive(Default, Clone)]
struct Counts { profiles: u64, matchings: usize, unique: u64, max: usize, total: u64 }
fn stable_counts(n: usize, k: usize, t: &Tables) -> (Counts, Vec<usize>) {
    let ns = t.r.len(); let mut c = Counts { matchings: t.m.len(), ..Default::default() }; let mut per = vec![];
    for pa in 0..ns { for pb in 0..ns {
        let s = (0..t.m.len()).filter(|&i| t.wa[pa][i] & t.wb[pb][i] == 0).count();
        if n <= 2 {
            let d = t.m.iter().filter(|&&mm| stable_direct(n, k, &t.r[pa], &t.r[pb], mm)).count();
            assert_eq!(s, d, "bit form and direct stability disagree");
        }
        assert!(s >= 1, "no stable matching");
        c.profiles += 1; c.unique += (s == 1) as u64; c.max = c.max.max(s); c.total += s as u64; per.push(s);
    } }
    (c, per)
}

// ---------------------------------------------------------------- paths to stability (paths.py)
#[derive(Default)]
struct PathRes { longest: usize, cyc: u64, unreach: u64 }
fn paths(n: usize, k: usize, t: &Tables) -> PathRes {
    let ns = t.r.len(); let nm = t.m.len();
    let mut index = vec![usize::MAX; 1 << (n * n)];
    for (i, &mm) in t.m.iter().enumerate() { index[mm as usize] = i; }
    let mut res = PathRes::default();
    for pa in 0..ns { for pb in 0..ns {
        let mut succ: Vec<Vec<usize>> = vec![vec![]; nm];
        for i in 0..nm {
            let x = t.m[i]; let mut blk = t.wa[pa][i] & t.wb[pb][i];
            while blk != 0 {
                let bit = blk & blk.wrapping_neg(); blk ^= bit;
                let q = bit.trailing_zeros() as usize; let (a, b) = (q / n, q % n);
                let y = (x & !t.da[pa][i][a] & !t.db[pb][i][b]) | bit;
                let j = index[y as usize]; assert!(j != usize::MAX, "a move left the matchings");
                succ[i].push(j);
            }
            if n <= 2 { assert_eq!(succ[i].is_empty(), stable_direct(n, k, &t.r[pa], &t.r[pb], x)); }
        }
        let mut pred: Vec<Vec<usize>> = vec![vec![]; nm];
        for i in 0..nm { for &j in &succ[i] { pred[j].push(i); } }
        let mut dist = vec![usize::MAX; nm]; let mut todo = VecDeque::new();
        for i in 0..nm { if succ[i].is_empty() { dist[i] = 0; todo.push_back(i); } }
        while let Some(j) = todo.pop_front() { for &i in &pred[j] { if dist[i] == usize::MAX { dist[i] = dist[j] + 1; todo.push_back(i); } } }
        let mut out: Vec<usize> = succ.iter().map(|s| s.len()).collect();
        let mut gone: VecDeque<usize> = (0..nm).filter(|&i| out[i] == 0).collect(); let mut left = nm;
        while let Some(j) = gone.pop_front() { left -= 1; for &i in &pred[j] { out[i] -= 1; if out[i] == 0 { gone.push_back(i); } } }
        let bad = dist.iter().filter(|&&d| d == usize::MAX).count();
        res.unreach += bad as u64; res.cyc += (left > 0) as u64;
        res.longest = res.longest.max(dist.iter().filter(|&&d| d != usize::MAX).copied().max().unwrap());
    } }
    res
}

// ---------------------------------------------------------------- polytopes (field.py), exact
#[derive(Clone)]
struct Con { c: Vec<i64>, rhs: Q } // c . x >= rhs
fn val(g: &Con, x: &[Q]) -> Q {
    let mut s = qi(0);
    for (a, &b) in g.c.iter().zip(x) { if *a != 0 { s = add(s, mul(qi(*a), b)); } }
    sub(s, g.rhs)
}
fn tight(cons: &[Con], x: &[Q]) -> u64 {
    assert!(cons.len() <= 64);
    cons.iter().enumerate().fold(0u64, |acc, (t, c)| if val(c, x).n == 0 { acc | 1 << t } else { acc })
}
fn boxp(d: usize) -> (Vec<Con>, Vec<Vec<Q>>) {
    let mut cons = vec![];
    for e in 0..d {
        cons.push(Con { c: (0..d).map(|f| (f == e) as i64).collect(), rhs: qi(0) });
        cons.push(Con { c: (0..d).map(|f| -((f == e) as i64)).collect(), rhs: qi(-1) });
    }
    let v = (0..1usize << d).map(|m| (0..d).map(|e| qi((m >> (d - 1 - e) & 1) as i64)).collect()).collect();
    (cons, v)
}
fn cut(d: usize, cons: &[Con], v: &[Vec<Q>], g: &Con) -> Vec<Vec<Q>> {
    let z: Vec<u64> = v.iter().map(|x| tight(cons, x)).collect();
    let s: Vec<Q> = v.iter().map(|x| val(g, x)).collect();
    let mut out: Vec<Vec<Q>> = (0..v.len()).filter(|&i| sign(s[i]) >= 0).map(|i| v[i].clone()).collect();
    for i in (0..v.len()).filter(|&i| sign(s[i]) > 0) {
        for j in (0..v.len()).filter(|&j| sign(s[j]) < 0) {
            let zz = z[i] & z[j];
            if (zz.count_ones() as usize) + 1 < d { continue; }
            if (0..v.len()).any(|u| u != i && u != j && z[u] & zz == zz) { continue; }
            let t = div(s[i], sub(s[i], s[j]));
            out.push(v[i].iter().zip(&v[j]).map(|(&a, &b)| add(a, mul(t, sub(b, a)))).collect());
        }
    }
    out.sort(); out.dedup(); out
}
fn solve(a: &[Vec<i64>], b: &[Q]) -> Option<Vec<Q>> {
    let n = a.len();
    let mut m: Vec<Vec<Q>> = a.iter().zip(b).map(|(row, &r)| { let mut x: Vec<Q> = row.iter().map(|&v| qi(v)).collect(); x.push(r); x }).collect();
    for c in 0..n {
        let p = (c..n).find(|&r| m[r][c].n != 0)?;
        m.swap(c, p);
        for r in 0..n { if r != c && m[r][c].n != 0 {
            let f = div(m[r][c], m[c][c]); let rowc = m[c].clone();
            for (x, y) in m[r].iter_mut().zip(rowc) { *x = sub(*x, mul(f, y)); }
        } }
    }
    Some((0..n).map(|i| div(m[i][n], m[i][i])).collect())
}
fn vertices_brute(d: usize, cons: &[Con]) -> Vec<Vec<Q>> {
    // every d-subset of the inequalities made tight (d <= 4 here)
    let mut out = vec![]; let nc = cons.len(); let mut idx: Vec<usize> = (0..d).collect();
    loop {
        let a: Vec<Vec<i64>> = idx.iter().map(|&i| cons[i].c.clone()).collect();
        let b: Vec<Q> = idx.iter().map(|&i| cons[i].rhs).collect();
        if let Some(x) = solve(&a, &b) { if cons.iter().all(|c| sign(val(c, &x)) >= 0) { out.push(x); } }
        let mut p = d; loop { if p == 0 { out.sort(); out.dedup(); return out; } p -= 1; if idx[p] < nc - d + p { break; } }
        idx[p] += 1; for q in p + 1..d { idx[q] = idx[q - 1] + 1; }
    }
}
fn degree_cons(n: usize, k: Q) -> Vec<Con> {
    let mut out = vec![]; let nk = Q { n: a_neg(k.n), d: k.d };
    for i in 0..n { out.push(Con { c: (0..n * n).map(|e| -((e / n == i) as i64)).collect(), rhs: nk }); }
    for j in 0..n { out.push(Con { c: (0..n * n).map(|e| -((e % n == j) as i64)).collect(), rhs: nk }); }
    out
}
fn stab_cons(n: usize, ra: &[Vec<u8>], rb: &[Vec<u8>], k: i64) -> Vec<Con> {
    let mut out = vec![];
    for i in 0..n { for j in 0..n {
        let mut c = vec![0i64; n * n]; c[i * n + j] = k;
        for j2 in 0..n { if ra[i][j2] < ra[i][j] { c[i * n + j2] += 1; } }
        for i2 in 0..n { if rb[j][i2] < rb[j][i] { c[i2 * n + j] += 1; } }
        out.push(Con { c, rhs: qi(k) });
    } }
    out
}
fn point(n: usize, m: u16) -> Vec<Q> { (0..n * n).map(|e| qi((m >> e & 1) as i64)).collect() }
fn dd(d: usize, start: (Vec<Con>, Vec<Vec<Q>>), extra: &[Con]) -> (Vec<Con>, Vec<Vec<Q>>) {
    let (mut cons, mut v) = start;
    for g in extra { v = cut(d, &cons, &v, g); cons.push(g.clone()); }
    (cons, v)
}

/// the k=1 stable polytope on one profile: assert integral corners = stable matchings; return the corner count
fn stable_polytope(n: usize, base: &(Vec<Con>, Vec<Vec<Q>>), ra: &[Vec<u8>], rb: &[Vec<u8>], m1: &[u16], stable: &[bool]) -> usize {
    let (_, v) = dd(n * n, base.clone(), &stab_cons(n, ra, rb, 1));
    assert!(v.iter().all(|x| x.iter().all(|q| q.d == 1)), "a fractional vertex of the stable polytope");
    let mut want: Vec<Vec<Q>> = m1.iter().zip(stable).filter(|(_, &s)| s).map(|(&mm, _)| point(n, mm)).collect();
    want.sort();
    assert!(v == want, "stable polytope vertices differ from the stable matchings");
    v.len()
}
fn base_polytope(n: usize) -> (Vec<Con>, Vec<Vec<Q>>) {
    let base = dd(n * n, boxp(n * n), &degree_cons(n, qi(1)));
    let mut want: Vec<Vec<Q>> = matchings(n, 1).iter().map(|&m| point(n, m)).collect(); want.sort();
    assert!(base.1 == want, "the matching polytope is not the matchings");
    base
}

// ---------------------------------------------------------------- symmetry reduction, k = 1
/// Group G = relabel A (tau) x relabel B (sigma), |G| = (n!)^2. A profile (pa, pb) goes to
/// pa'[tau a] = sigma o pa[a], pb'[sigma b] = tau o pb[b]. Orbits: representatives of pa under G,
/// then representatives of pb under the stabiliser H of pa. Weight of (pa, pb) = |G| / |Stab_H(pb)|,
/// which is the size of its G-orbit. Returns (orbits, weight sum, unique, max, total stable, histogram).
struct Orbit { orbits: u64, weight: u128, unique: u128, max: usize, total: u128, hist: Vec<u128>, ex: (usize, usize) }
fn orbit_k1(n: usize, threads: usize) -> Orbit {
    let ps = perms(n); let f = ps.len(); let ns = f.pow(n as u32);
    let pidx: HashMap<Vec<u8>, usize> = ps.iter().enumerate().map(|(i, p)| (p.clone(), i)).collect();
    // comp[s][p]: index of the permutation p with each entry x replaced by s[x]
    let comp: Vec<Vec<usize>> = ps.iter().map(|s| ps.iter().map(|p| pidx[&p.iter().map(|&x| s[x as usize]).collect::<Vec<u8>>()]).collect()).collect();
    let digs: Vec<Vec<usize>> = (0..ns).map(|s| { let mut x = s; let mut d = vec![0; n]; for a in (0..n).rev() { d[a] = x % f; x /= f; } d }).collect();
    let enc = |d: &[usize]| d.iter().fold(0usize, |acc, &x| acc * f + x);
    // act on a side tuple: rows permuted by `rows`, entries relabelled by `ent`
    let act = |rows: usize, ent: usize, s: usize| { let mut nd = vec![0; n]; for a in 0..n { nd[ps[rows][a] as usize] = comp[ent][digs[s][a]]; } enc(&nd) };
    let g: Vec<(usize, usize)> = (0..f).flat_map(|t| (0..f).map(move |s| (t, s))).collect();
    let gsize = g.len() as u128;
    // representatives of pa
    let mut reps: Vec<(usize, Vec<(usize, usize)>)> = vec![]; let mut pa_weight: u128 = 0;
    for s in 0..ns {
        let mut canon = true; let mut h = vec![];
        for &(t, sg) in &g { let y = act(t, sg, s); if y < s { canon = false; break; } if y == s { h.push((t, sg)); } }
        if canon { pa_weight += gsize / h.len() as u128; reps.push((s, h)); }
    }
    assert_eq!(pa_weight, ns as u128, "pa orbit sizes do not sum to (n!)^n");
    // B side "would join" bits per side tuple and matching (k=1), fast form, checked against side_bits on n <= 3
    let m1 = matchings(n, 1); let nm = m1.len();
    let mate: Vec<Vec<Option<usize>>> = m1.iter().map(|&m| (0..n).map(|b| (0..n).find(|&a| m >> (a * n + b) & 1 == 1)).collect()).collect();
    let rk: Vec<Vec<Vec<u8>>> = (0..ns).map(|s| ranks(&digs[s].iter().map(|&p| ps[p].clone()).collect::<Vec<_>>())).collect();
    let mut wb = vec![0u16; ns * nm];
    for s in 0..ns { for (i, &m) in m1.iter().enumerate() {
        let mut bits = 0u16;
        for b in 0..n { for a in 0..n {
            let free = match mate[i][b] { None => true, Some(p) => p != a && rk[s][b][a] < rk[s][b][p] };
            if free && mate[i][b] != Some(a) { bits |= 1 << (a * n + b); }
        } }
        if n <= 3 { assert_eq!(bits, side_bits(n, 1, &rk[s], m, 1), "fast B bits differ"); }
        wb[s * nm + i] = bits;
    } }
    let act_b = |h: (usize, usize), s: usize| act(h.1, h.0, s); // pb rows relabelled by sigma, entries by tau
    let work = |part: usize| {
        let mut o = Orbit { orbits: 0, weight: 0, unique: 0, max: 0, total: 0, hist: vec![0; 64], ex: (0, 0) };
        for (ri, (pa, h)) in reps.iter().enumerate() {
            if ri % threads != part { continue; }
            let wa: Vec<u16> = m1.iter().map(|&m| side_bits(n, 1, &rk[*pa], m, 0)).collect();
            for pb in 0..ns {
                let mut stab = 1u128;
                if h.len() > 1 {
                    stab = 0; let mut skip = false;
                    for &x in h { let y = act_b(x, pb); if y < pb { skip = true; break; } if y == pb { stab += 1; } }
                    if skip { continue; }
                }
                assert!(gsize % stab == 0);
                let w = gsize / stab; let row = &wb[pb * nm..pb * nm + nm];
                let c = wa.iter().zip(row).filter(|(x, y)| *x & *y == 0).count();
                assert!(c >= 1, "no stable matching");
                o.orbits += 1; o.weight += w; o.unique += if c == 1 { w } else { 0 }; if c > o.max { o.max = c; o.ex = (*pa, pb); }
                o.total += w * c as u128; o.hist[c] += w;
            }
        }
        o
    };
    let parts: Vec<Orbit> = std::thread::scope(|sc| {
        let hs: Vec<_> = (0..threads).map(|p| { let work = &work; sc.spawn(move || work(p)) }).collect();
        hs.into_iter().map(|h| h.join().unwrap()).collect()
    });
    let mut o = Orbit { orbits: 0, weight: 0, unique: 0, max: 0, total: 0, hist: vec![0; 64], ex: (0, 0) };
    for p in parts { o.orbits += p.orbits; o.weight += p.weight; o.unique += p.unique; if p.max > o.max { o.max = p.max; o.ex = p.ex; } o.total += p.total; for (a, b) in o.hist.iter_mut().zip(p.hist) { *a += b; } }
    assert_eq!(o.weight, (f as u128).pow(2 * n as u32), "orbit weights do not sum to (n!)^(2n)");
    let rows = |s: usize| format!("[{}]", digs[s].iter().map(|&p| seq(&ps[p])).collect::<Vec<_>>().join(", "));
    eprintln!("n={} a profile with {} stable matchings: pa={} pb={}", n, o.max, rows(o.ex.0), rows(o.ex.1));
    if n == 4 { println!("{{\"example\": {{\"n\": 4, \"stable\": {}, \"pa\": {}, \"pb\": {}}}}}", o.max, rows(o.ex.0), rows(o.ex.1)); }
    o
}

fn seq<T: std::fmt::Display>(xs: &[T]) -> String { format!("[{}]", xs.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(", ")) }
fn line(name: &str, xs: String) { println!("{{\"name\": \"{}\", \"seq\": {}}}", name, xs); }

fn mode_diff() {
    let t0 = Instant::now();
    // check.py
    let mut c: HashMap<(usize, usize), Counts> = HashMap::new(); let mut per1: HashMap<usize, Vec<usize>> = HashMap::new();
    let mut tabs: HashMap<(usize, usize), Tables> = HashMap::new();
    for k in [1, 2] { for n in 1..=3 {
        let t = tables(n, k); let (cc, per) = stable_counts(n, k, &t);
        if k == 1 { per1.insert(n, per); }
        c.insert((n, k), cc); tabs.insert((n, k), t);
    } }
    let g = |f: &dyn Fn(&Counts) -> u64, k: usize| seq(&(1..=3).map(|n| f(&c[&(n, k)])).collect::<Vec<_>>());
    line("preference profiles, n=1..3", g(&|x| x.profiles, 1));
    line("one-to-one matchings (capacity 1), n=1..3", g(&|x| x.matchings as u64, 1));
    line("capacity-2 matchings, n=1..3", g(&|x| x.matchings as u64, 2));
    line("profiles with a unique stable matching k=1, n=1..3", g(&|x| x.unique, 1));
    line("profiles with a unique stable matching k=2, n=1..3", g(&|x| x.unique, 2));
    line("most stable matchings on one profile k=1, n=1..3", g(&|x| x.max as u64, 1));
    line("most stable matchings on one profile k=2, n=1..3", g(&|x| x.max as u64, 2));
    // extras the Python prints but does not fingerprint (compared against check.py output by native_diff.py)
    line("native extra: stable matchings summed over profiles k=1, n=1..3", g(&|x| x.total, 1));
    line("native extra: stable matchings summed over profiles k=2, n=1..3", g(&|x| x.total, 2));
    // the symmetry reduction against the direct counts, n = 1..3
    for n in 1..=3 {
        let o = orbit_k1(n, 1); let d = &c[&(n, 1)];
        assert!(o.unique == d.unique as u128 && o.max == d.max && o.total == d.total as u128, "orbit counts differ from direct, n={}", n);
        eprintln!("orbit method n={}: {} orbits, weights sum to {} = (n!)^(2n), unique/max/total equal the direct counts", n, o.orbits, o.weight);
    }
    // paths.py
    for k in [1, 2] {
        let r: Vec<PathRes> = (1..=3).map(|n| paths(n, k, &tabs[&(n, k)])).collect();
        line(&format!("longest shortest path to stability k={}, n=1..3", k), seq(&r.iter().map(|x| x.longest).collect::<Vec<_>>()));
        line(&format!("profiles with a cycle of blocking-pair moves k={}, n=1..3", k), seq(&r.iter().map(|x| x.cyc).collect::<Vec<_>>()));
        line(&format!("start matchings that cannot reach stability k={}, n=1..3", k), seq(&r.iter().map(|x| x.unreach).collect::<Vec<_>>()));
    }
    // field.py: double description = brute force on n = 2
    let ps2 = perms(2); let sd2 = sides(2, &ps2); let r2: Vec<_> = sd2.iter().map(|s| ranks(s)).collect();
    for pa in &r2 { for pb in &r2 {
        let mut extra = degree_cons(2, qi(1)); extra.extend(stab_cons(2, pa, pb, 1));
        let (cons, v) = dd(4, boxp(4), &extra); assert!(v == vertices_brute(4, &cons), "dd and brute disagree");
    } }
    for k in [qi(1), mk(3, 2), qi(2)] { let (cons, v) = dd(4, boxp(4), &degree_cons(2, k)); assert!(v == vertices_brute(4, &cons)); }
    // stable polytope: n=2 all, n=3 every 97th profile in check.profiles order
    let mut tot = vec![];
    for n in [2usize, 3] {
        let t = &tabs[&(n, 1)]; let base = base_polytope(n); let ns = t.r.len(); let mut sum = 0;
        for pa in 0..ns { for pb in 0..ns {
            let idx = pa * ns + pb; if n == 3 && idx % 97 != 0 { continue; }
            let st: Vec<bool> = (0..t.m.len()).map(|i| t.wa[pa][i] & t.wb[pb][i] == 0).collect();
            sum += stable_polytope(n, &base, &t.r[pa], &t.r[pb], &t.m, &st);
        } }
        tot.push(sum);
    }
    line("stable polytope k=1 vertices summed, n=2 all profiles, n=3 sample (every 97th)", seq(&tot));
    // direct k=2 stability inequality: profiles where it admits an unstable 0/1 point
    let mut naive = vec![];
    for n in [2usize, 3] {
        let t = &tabs[&(n, 2)]; let ns = t.r.len(); let mut cnt = 0;
        for pa in 0..ns { for pb in 0..ns {
            let idx = pa * ns + pb; if n == 3 && idx % 97 != 0 { continue; }
            let sc = stab_cons(n, &t.r[pa], &t.r[pb], 2); let mut bad = false;
            for (i, &m) in t.m.iter().enumerate() {
                let ok = sc.iter().all(|g| sign(val(g, &point(n, m))) >= 0); let st = t.wa[pa][i] & t.wb[pb][i] == 0;
                if st { assert!(ok, "a stable matching breaks the k-stability inequality"); }
                bad |= ok && !st;
            }
            cnt += bad as u64;
        } }
        naive.push(cnt);
    }
    line("profiles where direct k=2 stability admits unstable points, n=2..3", seq(&naive));
    // b-matching polytope with capacity k in {1, 3/2, 2}
    let mut bm: HashMap<&str, Vec<usize>> = HashMap::new();
    for n in [2usize, 3] { for (name, k) in [("1", qi(1)), ("3/2", mk(3, 2)), ("2", qi(2))] {
        let (_, v) = dd(n * n, boxp(n * n), &degree_cons(n, k));
        let frac = v.iter().filter(|x| x.iter().any(|q| q.d != 1)).count();
        bm.entry(name).or_default().push(v.len()); bm.entry(if name == "3/2" { "f3/2" } else { "-" }).or_default().push(frac);
    } }
    line("b-matching polytope vertices k=1, n=2..3", seq(&bm["1"]));
    line("b-matching polytope vertices k=3/2, n=2..3", seq(&bm["3/2"]));
    line("b-matching polytope fractional vertices k=3/2, n=2..3", seq(&bm["f3/2"]));
    line("b-matching polytope vertices k=2, n=2..3", seq(&bm["2"]));
    eprintln!("diff mode: {:.2} s", t0.elapsed().as_secs_f64());
    let _ = per1;
}

fn mode_new(threads: usize) {
    // (a) stable polytope, k=1, all 46656 profiles at n = 3
    let t0 = Instant::now();
    let n = 3; let t = tables(n, 1); let base = base_polytope(n); let ns = t.r.len();
    let mut hist = vec![0u64; 8]; let mut sum = 0usize;
    let rows: Vec<usize> = (0..ns).collect();
    let parts: Vec<(Vec<u64>, usize)> = std::thread::scope(|sc| {
        let hs: Vec<_> = (0..threads).map(|p| { let (t, base, rows) = (&t, &base, &rows); sc.spawn(move || {
            let mut h = vec![0u64; 8]; let mut s = 0;
            for &pa in rows.iter().filter(|&&r| r % threads == p) { for pb in 0..ns {
                let st: Vec<bool> = (0..t.m.len()).map(|i| t.wa[pa][i] & t.wb[pb][i] == 0).collect();
                let v = stable_polytope(n, base, &t.r[pa], &t.r[pb], &t.m, &st); h[v] += 1; s += v;
            } }
            (h, s)
        }) }).collect();
        hs.into_iter().map(|h| h.join().unwrap()).collect()
    });
    for (h, s) in parts { for (a, b) in hist.iter_mut().zip(h) { *a += b; } sum += s; }
    let profiles: u64 = hist.iter().sum(); assert_eq!(profiles, 46656);
    line("native: stable polytope k=1, n=3, all profiles: profiles, vertices summed", seq(&[profiles as usize, sum]));
    line("native: stable polytope k=1, n=3, profiles with 1, 2, 3 vertices", seq(&hist[1..4]));
    println!("{{\"name\": \"native: seconds, stable polytope n=3 all\", \"seq\": [{}]}}", t0.elapsed().as_secs());
    // (b) n = 1..4 at k = 1 by symmetry reduction
    let mut os = vec![];
    for n in 1..=4 { let t1 = Instant::now(); let o = orbit_k1(n, threads); eprintln!("orbit n={}: {} orbits, {:.1} s", n, o.orbits, t1.elapsed().as_secs_f64()); os.push((o, t1.elapsed().as_secs())); }
    line("native: profile orbits under relabelling A and B, n=1..4", seq(&os.iter().map(|o| o.0.orbits).collect::<Vec<_>>()));
    line("native: orbit weights summed, equal to (n!)^(2n), n=1..4", seq(&os.iter().map(|o| o.0.weight).collect::<Vec<_>>()));
    line("native: profiles with a unique stable matching k=1, n=1..4", seq(&os.iter().map(|o| o.0.unique).collect::<Vec<_>>()));
    line("native: most stable matchings on one profile k=1, n=1..4", seq(&os.iter().map(|o| o.0.max).collect::<Vec<_>>()));
    line("native: stable matchings summed over profiles k=1, n=1..4", seq(&os.iter().map(|o| o.0.total).collect::<Vec<_>>()));
    let o4 = &os[3].0;
    line("native: n=4 k=1 profiles by number of stable matchings, 1..max", seq(&o4.hist[1..=o4.max]));
    println!("{{\"name\": \"native: seconds, n=4 orbit count\", \"seq\": [{}]}}", os[3].1);
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let threads = 2; // the machine is shared: at most 2 threads
    match args.get(1).map(|s| s.as_str()) {
        Some("diff") => mode_diff(),
        Some("new") => mode_new(threads),
        _ => { eprintln!("usage: love-native diff | new"); std::process::exit(2); }
    }
    println!("PASS");
}
