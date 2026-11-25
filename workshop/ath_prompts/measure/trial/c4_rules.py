"""C4 proxy: does a rule in the system prompt get followed as often when written informally vs formally?
Rule-following by a model, not memory by a person. Usage: c4_rules.py MODEL OUT.json"""
import json,os,re,sys
os.environ.setdefault("HF_HUB_OFFLINE","1")
import torch
from transformers import AutoTokenizer,AutoModelForCausalLM
from math import comb
torch.set_num_threads(4)
RULES=[ # (informal, formal, checker)
 ("always end ur answer w the word DONE","Always end your answer with the word DONE.",lambda o:o.strip().rstrip(".!").endswith("DONE")),
 ("start every reply w 'ok so'","Begin every reply with the words \"ok so\".",lambda o:o.strip().lower().startswith("ok so")),
 ("never use the letter z lol","Never use the letter z.",lambda o:"z" not in o.lower()),
 ("all lowercase pls, no caps","Write entirely in lowercase letters; do not use capital letters.",lambda o:o==o.lower()),
 ("keep it under 20 words","Keep your answer under 20 words.",lambda o:len(o.split())<20),
 ("say 4 instead of for","Write the digit 4 instead of the word \"for\".",lambda o:not re.search(r"\bfor\b",o,re.I)),
 ("no bullet points or lists","Do not use bullet points or lists.",lambda o:not re.search(r"^\s*([-*•]|\d+\.)\s",o,re.M)),
 ("put ur answer in ALL CAPS","Write your answer in capital letters only.",lambda o:o==o.upper()),
 ("include the word banana somewhere","Include the word \"banana\" somewhere in your answer.",lambda o:"banana" in o.lower()),
 ("never say sorry","Never use the word \"sorry\".",lambda o:"sorry" not in o.lower()),
]
QS=["What is the capital of France?","Give me one tip for sleeping better.","Explain what a prime number is.","What should I cook for dinner tonight?"]
def main(model,outp):
    tok=AutoTokenizer.from_pretrained(model); tok.padding_side="left"
    m=AutoModelForCausalLM.from_pretrained(model,torch_dtype=torch.float32).eval()
    items=[(ri,reg,q) for ri in range(len(RULES)) for reg in (0,1) for q in QS]
    P=[tok.apply_chat_template([{"role":"system","content":RULES[ri][reg]},{"role":"user","content":q}],tokenize=False,add_generation_prompt=True) for ri,reg,q in items]
    outs=[]
    for i in range(0,len(P),16):
        enc=tok(P[i:i+16],return_tensors="pt",padding=True)
        with torch.no_grad(): g=m.generate(**enc,max_new_tokens=80,do_sample=False,pad_token_id=tok.eos_token_id)
        outs+=tok.batch_decode(g[:,enc.input_ids.shape[1]:],skip_special_tokens=True)
    rows=[dict(rule=ri,register=("informal","formal")[reg],q=q,ok=bool(RULES[ri][2](o)),output=o) for (ri,reg,q),o in zip(items,outs)]
    json.dump(dict(model=model,rows=rows),open(outp,"w"),indent=1)
    I=sum(r["ok"] for r in rows if r["register"]=="informal"); F=sum(r["ok"] for r in rows if r["register"]=="formal")
    b=c=0
    for ri in range(len(RULES)):
        for q in QS:
            x=[r["ok"] for r in rows if r["rule"]==ri and r["q"]==q]
            b+=x[0] and not x[1]; c+=x[1] and not x[0]
    n=b+c; p=min(1,2*sum(comb(n,k) for k in range(min(b,c)+1))/2**n) if n else 1
    print(f"{model}: informal {I}/40 formal {F}/40 informal-only {b} formal-only {c} exact McNemar p={p:.4f}")
    for ri in range(len(RULES)):
        print(ri,RULES[ri][0],"|",sum(r["ok"] for r in rows if r["rule"]==ri and r["register"]=="informal"),sum(r["ok"] for r in rows if r["rule"]==ri and r["register"]=="formal"))
if __name__=="__main__": main(sys.argv[1],sys.argv[2])
