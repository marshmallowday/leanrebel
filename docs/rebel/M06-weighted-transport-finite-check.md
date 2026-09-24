# Supplementary finite-law weighted transport check

This deterministic exact-Fraction calculation is supplementary evidence only.
It neither executes the Lean solver nor replaces compiler, lint or axiom gates.
Each case uses two correlated private-seed/query laws, independently varied OLD
and NEW four-atom distributions, bounded gains, signed model-value changes and
information-measurable density changes. NEW quality is calculated on its actual
support; a missing NEW conditional is never fabricated. The weighted upper
bound and its uniform comparison are checked without floating-point rounding.
The canonical protocol and biased-parent security are separately checked by Lean.

Run the code below with Python 3. It has no network access or Git operations.

```python
"""Independent exact finite-law check; not Lean or game-solver acceptance."""
from fractions import Fraction as F
from random import Random
import json
rng=Random(20260924)

def probability_law():
    while True:
        weights=[rng.randrange(5) for _ in range(4)]
        if sum(weights): return tuple(F(w,sum(weights)) for w in weights)

def conditional(p,tag):
    inds=range(2*tag,2*tag+2);mass=sum(p[i] for i in inds)
    return None if mass==0 else tuple(p[i]/mass for i in inds)

def mean(v,p): return sum(a*b for a,b in zip(v,p))

def main():
    support_lost=0;unequal_conditionals=0;strict=0
    for _ in range(10000):
        cases=[]
        for n in range(2):
            old,new=probability_law(),probability_law()
            gain=tuple(F(rng.randrange(-2,3)) for _ in range(4))
            change=tuple(F(rng.randrange(-4,5)) for _ in range(4))
            oc=[conditional(old,t) for t in range(2)]
            nc=[conditional(new,t) for t in range(2)]
            qual=max(F(0),*(mean(gain[2*t:2*t+2],nc[t]) for t in range(2) if nc[t]))
            # Information-measurable density changes the tag weights, not its hidden conditional.
            w=[rng.randrange(1,5),rng.randrange(1,5)]
            actual=[old[i]*w[i//2] for i in range(4)]
            z=sum(actual);actual=[a/z for a in actual]
            defect=[F(0) if oc[t] is None else F(1) if nc[t] is None else
                    sum(abs(x-y) for x,y in zip(oc[t],nc[t])) for t in range(2)]
            support_lost+=sum(oc[t] is not None and nc[t] is None for t in range(2))
            unequal_conditionals+=sum(oc[t] is not None and nc[t] is not None and oc[t]!=nc[t] for t in range(2))
            cases.append((gain,change,oc,actual,defect,qual))
        loss=max(x[-1] for x in cases)
        weighted=F(0);lhs=F(0);max_drift=F(0);max_transport=F(0)
        for n,(gain,change,oc,actual,defect,_) in enumerate(cases):
            seed=F(n+1,3)
            lhs+=seed*sum(actual[i]*(gain[i]+change[i]) for i in range(4))
            for tag in range(2):
                if oc[tag] is None: continue
                positive=max(F(0),mean(change[2*tag:2*tag+2],oc[tag]))
                charge=loss+positive+2*defect[tag]
                weighted+=seed*sum(actual[2*tag:2*tag+2])*charge
                max_drift=max(max_drift,positive);max_transport=max(max_transport,defect[tag])
        uniform=loss+max_drift+2*max_transport
        assert lhs<=weighted<=uniform,(cases,loss,lhs,weighted,uniform)
        strict+=weighted<uniform
    p=F(1,100)
    result={'cases':10000,'old_supported_new_missing_queries':support_lost,
            'unequal_supported_hidden_conditionals':unequal_conditionals,
            'strict_weighted_uniform_improvements':strict,
            'rare_query_cost':str(2*p),'maximum_query_cost':'2',
            'actual_coupled_disagreement_cost':'0',
            'independent_marginals_disagreement_cost':str(4*p*(1-p)),
            'all_exact_fraction_assertions_pass':True,
            'scope':'Generic finite-law algebra only; not Lean or protocol-level validation.'}
    print(json.dumps(result,indent=2))
if __name__=='__main__':main()
```

Observed output:

```json
{
  "cases": 10000,
  "old_supported_new_missing_queries": 1391,
  "unequal_supported_hidden_conditionals": 32962,
  "strict_weighted_uniform_improvements": 9999,
  "rare_query_cost": "1/50",
  "maximum_query_cost": "2",
  "actual_coupled_disagreement_cost": "0",
  "independent_marginals_disagreement_cost": "99/2500",
  "all_exact_fraction_assertions_pass": true,
  "scope": "Generic finite-law algebra only; not Lean or protocol-level validation."
}
```
