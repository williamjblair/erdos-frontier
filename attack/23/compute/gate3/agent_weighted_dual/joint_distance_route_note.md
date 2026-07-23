# Local route note: GB-2SUM

Status: **KILLED**.

The sufficient estimate

```text
D1 + D2 <= n + partnerDistance(d) - 2
```

fails in the strict all-nonbridge BF-RL residual.  The exact fixture and
cutwise composition proof are in
`joint_distance_counterexample_audit.md`; the executable certificate is
`joint_distance_counterexample.py` with its pytest regression.

The killed estimate was stronger than RL.  On the counterexample its linear
premise fails by one, while the actual quadratic cost has 2718 units of
slack (`3042 <= 5760`).  The next two-demand route must therefore retain
more geometry than the raw distance sum.  In particular it must recognize
that a capacity-two C4 chain moving a common demand endpoint adds four to
`D1+D2` per three new vertices but only adds

```text
[(D+3)^2 - (D+1)^2] * 2 = 8D + 16
```

to the two-demand cost per block step `D -> D+2`; the RL budget grows with
the simultaneously increasing slack.  A viable invariant should charge
these common series blocks directly rather than forbid them through an
order-only bound.
