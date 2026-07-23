#!/usr/bin/env python3
"""Attempt to run the author's complete_v2_cert.py (condition-4 verifier) with all
DETERMINISTIC inputs regenerated. cp_cache.pkl is synthesized as (ns0, dedge, [], [], None)
-- complete_v2_cert.py reads only ns0 and dedge from it, both regenerated combinatorial
data. Expected outcome: the run stops at horn_cert_state_it16.pkl (the envelope-row
certificate data saved inside the author's LP cutting-plane loop), which is neither in
the arXiv package nor on GitHub. This isolates the untrusted remainder to that one file.
"""
import os, pickle, shutil, subprocess, sys
HERE = os.path.dirname(os.path.abspath(__file__))
ANC = os.path.join(HERE, "..", "src", "anc")
os.chdir(HERE)

states9, dedge9, moments = pickle.load(open("my_moments_n9.pkl", "rb"))
pickle.dump((len(states9), dedge9, [], [], None), open("cp_cache.pkl", "wb"), protocol=4)
print(f"synthesized cp_cache.pkl (ns0={len(states9)}, dedge; rows/provtypes empty)")

# author's cache format for prove_cert.load(9): cache_n9.pkl with keys used downstream.
# complete_v2_cert.py uses only C['moments'] and C['states']; supply exactly those from
# the regenerated tables (moments tuples need the (lab,tt,sigma,flags,s,Pf,Pint) shape;
# Pf is unused by the verifier -> None placeholder).
moms_full = [(lab, tt, sigma, flags, s, None, Pint) for (lab, tt, sigma, flags, s, Pint) in moments]
pickle.dump(dict(N=9, states=states9, dedge=dedge9, moments=moms_full),
            open("cache_n9.pkl", "wb"), protocol=4)
print("wrote cache_n9.pkl (states/dedge/moments from regenerated tables)")

for f in ["horn_dual.pkl", "moment_gram_w.pkl", "mom_term_exact.pkl"]:
    shutil.copy(os.path.join(ANC, f), f)
print("copied shipped certificate pickles (horn_dual, moment_gram_w, mom_term_exact)")
print("NOT present (unavailable anywhere):", "horn_cert_state_it16.pkl")
print("--- running author's complete_v2_cert.py ---", flush=True)
env = dict(os.environ, PYTHONPATH=HERE)
r = subprocess.run([sys.executable, os.path.join(ANC, "complete_v2_cert.py")],
                   capture_output=True, text=True, cwd=HERE, env=env)
print(r.stdout[-3000:])
print(r.stderr[-2000:])
print(f"exit code: {r.returncode}")
