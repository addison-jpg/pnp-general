import json,sys,urllib.request,urllib.parse,re,html
def get(u):
    return json.load(urllib.request.urlopen(urllib.request.Request(u,headers={"User-Agent":"research-crawler/0.1","Accept":"application/json"}),timeout=60))
for t in sys.argv[1:]:
    d=get("https://api.zbmath.org/v1/document/_search?search_string="+urllib.parse.quote('ti:"'+t+'"')+"&results_per_page=3")
    res=d.get('result') or []
    print('##',t,'->',len(res))
    for r in res[:2]:
        ti=(r.get('title') or {}).get('title'); yr=r.get('year'); 
        auth=[a.get('name') for a in ((r.get('contributors') or {}).get('authors') or [])]
        src=[s.get('series',[{}]) for s in (r.get('source') or [])] if False else ''
        rev=' '.join(x.get('text','') for x in (r.get('editorial_contributions') or []))
        rev=re.sub(r'\s+',' ',html.unescape(re.sub('<[^>]+>','',rev)))
        print('  ',r.get('identifier'),yr,ti,'|',auth)
        print('   REVIEW:',rev[:1500] or '(none)')
