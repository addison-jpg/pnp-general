#!/usr/bin/env python3
"""Dump one of YOUR public Tumblr blogs to plain text, on YOUR machine, into a folder you choose
(keep that folder OUTSIDE the repository; this script never writes into git).

Setup (once): register an app at https://www.tumblr.com/oauth/apps to get a consumer key (api_key).
Usage:  python3 dump_tumblr.py BLOG_NAME API_KEY OUT_DIR [search_term]
  e.g.  python3 dump_tumblr.py asteroidxface.tumblr.com YOURKEY ~/diaries/asteroidxface beauvoir
Uses only the public read API and the standard library. Pages through all posts, saves one .txt per post.
"""
import json, os, re, sys, time, urllib.parse, urllib.request

def get(url):
    with urllib.request.urlopen(url, timeout=30) as r:
        return json.load(r)

def strip(html):
    return re.sub(r"\s+", " ", re.sub(r"<[^>]+>", " ", html or "")).strip()

def main():
    if len(sys.argv) < 4:
        sys.exit(__doc__)
    blog, key, out = sys.argv[1], sys.argv[2], os.path.expanduser(sys.argv[3])
    term = sys.argv[4] if len(sys.argv) > 4 else None
    os.makedirs(out, exist_ok=True)
    offset, total = 0, 0
    while True:
        q = {"api_key": key, "limit": 20, "offset": offset, "npf": "false"}
        if term: q["tag"] = term
        data = get(f"https://api.tumblr.com/v2/blog/{blog}/posts?" + urllib.parse.urlencode(q))
        posts = data.get("response", {}).get("posts", [])
        if not posts: break
        for p in posts:
            name = f"{p.get('date','')[:10]}_{p['id']}.txt"
            body = strip(p.get("body") or p.get("text") or "")
            with open(os.path.join(out, name), "w", encoding="utf-8") as f:
                f.write(f"{p.get('date','')}\n{p.get('post_url','')}\n\n{body}\n")
            total += 1
        offset += len(posts)
        time.sleep(1)   # be polite to the API
    print(f"saved {total} posts to {out}")

if __name__ == "__main__":
    main()
