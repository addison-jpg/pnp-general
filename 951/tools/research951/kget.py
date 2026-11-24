import sys,json,urllib.request,os
B="https://repository.kulib.kyoto-u.ac.jp/server/api"
def g(u):
    r=urllib.request.Request(u,headers={"User-Agent":"Mozilla/5.0","Accept":"application/json"})
    return json.load(urllib.request.urlopen(r,timeout=60))
for h in sys.argv[2:]:
    try:
        it=g(B+"/pid/find?id=hdl:"+h)
        for b in g(it["_links"]["bundles"]["href"])["_embedded"]["bundles"]:
            if b["name"]!="ORIGINAL": continue
            for s in g(b["_links"]["bitstreams"]["href"])["_embedded"]["bitstreams"]:
                fn=os.path.join(sys.argv[1],h.replace('/','_')+".pdf")
                r=urllib.request.Request(s["_links"]["content"]["href"],headers={"User-Agent":"Mozilla/5.0"})
                open(fn,"wb").write(urllib.request.urlopen(r,timeout=120).read()); print("ok",h,os.path.getsize(fn))
    except Exception as e: print("fail",h,e)
