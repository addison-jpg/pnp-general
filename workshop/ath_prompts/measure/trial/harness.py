"""C3 trial: informal vs formal asks, same content. Usage: harness.py MODEL OUT.json"""
import json,os,re,sys,time,signal
os.environ.setdefault("HF_HUB_OFFLINE","1")
import torch
from transformers import AutoTokenizer,AutoModelForCausalLM
torch.set_num_threads(4)
D=os.path.dirname(os.path.abspath(__file__))
CASE_SENSITIVE={"st02","st06"}

def score(task,out):
    """Blind to register: sees only the output text and the task's checker."""
    k,ans=task["kind"],task["answer"]
    if k=="num":
        nums=re.findall(r"-?\d+(?:\.\d+)?",out.replace(",",""))
        return bool(nums) and float(nums[-1])==float(ans)
    if k=="contains":
        return ans in out if task["id"] in CASE_SENSITIVE else ans.lower() in out.lower()
    if k=="py":
        m=re.findall(r"```(?:python)?\n(.*?)```",out,re.S)
        code=m[0] if m else "\n".join(l for l in out.splitlines() if l.startswith(("def ","f =","f=","    ")))
        try:
            signal.alarm(2); g={}; exec(code,g); exec(ans,g); signal.alarm(0); return True
        except BaseException:
            signal.alarm(0); return False

def main(model,outp):
    tasks=json.load(open(os.path.join(D,"tasks.json")))
    tok=AutoTokenizer.from_pretrained(model); tok.padding_side="left"
    m=AutoModelForCausalLM.from_pretrained(model,torch_dtype=torch.float32).eval()
    asks=[(t,r) for t in tasks for r in ("informal","formal")]
    prompts=[tok.apply_chat_template([{"role":"user","content":t[r]}],tokenize=False,add_generation_prompt=True) for t,r in asks]
    runs={"greedy":None,"s0":0,"s1":1,"s2":2}
    rows=[]; t0=time.time()
    for name,seed in runs.items():
        outs=[]
        for i in range(0,len(prompts),12):
            enc=tok(prompts[i:i+12],return_tensors="pt",padding=True)
            kw=dict(max_new_tokens=120,pad_token_id=tok.eos_token_id)
            if seed is None: kw["do_sample"]=False
            else: torch.manual_seed(1000*seed+i); kw.update(do_sample=True,temperature=0.7,top_p=1.0,top_k=0)
            with torch.no_grad(): g=m.generate(**enc,**kw)
            for row in g[:,enc.input_ids.shape[1]:]:
                ids=[x for x in row.tolist() if x!=tok.eos_token_id and x!=tok.pad_token_id]
                outs.append((tok.decode(ids,skip_special_tokens=True),len(ids)))
            print(name,i,round(time.time()-t0),flush=True)
        for (t,r),(o,n),p in zip(asks,outs,prompts):
            rows.append(dict(run=name,task=t["id"],register=r,ask_tokens=len(tok(t[r]).input_ids),out_tokens=n,ok=score(t,o),output=o))
    json.dump(dict(model=model,seconds=round(time.time()-t0),rows=rows),open(outp,"w"),indent=1)

if __name__=="__main__": main(sys.argv[1],sys.argv[2])
