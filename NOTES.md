# Notes on Preliminary Evaluation

### Example: _CFG elaboration_

Following example has runtime `B - A`, but `paicc` fails as no local-growth rate for `A` and `B` can be established for the loop.
The problem here is that `C` and `D` can be chosen arbitrarily big. Though the guard is not satisfied for `C + D >= B`. 

```
(COMMENT Brockschmidt_16/FGPSF09/VMCAI04/complete1.koat)
(GOAL COMPLEXITY)
(STARTTERM (FUNCTIONSYMBOLS start))
(VAR A B)
(RULES
  start(A, B) -> eval(A, B)
  eval(A, B)  -> eval(A - C, B + D) [ A >= B + 1 /\ C >= 0 /\ D >= 1 ]
  eval(A, B)  -> exit(A, B)
)
```

A possible solution is to elaborate the CFG with respect to the guard constraints, taking into account the guards of the possible successors.

```
(RULES
  start(A, B)    -> eval[tt](A, B) [ A >= B ]
  start(A, B)    -> eval[ff](A, B) [ A <  B ]
  eval[tt](A, B) -> eval[tt](A - C, B + D) [ A >= B + 1 /\ C >= 0 /\ D >= 1 /\ A - C > B + D ]
  eval[tt](A, B) -> eval[ff](A, B) [ A < B]
  eval[ff](A,B)  -> exit(A,B) [A < B]
)
```

### Example: _K is for constant_


Following example has constant runtime, but `paicc` infers `PRIMREC`.

```
(COMMENT Brockschmidt_16/T2/array_free.koat-ai)
(GOAL COMPLEXITY)
(STARTTERM (FUNCTIONSYMBOLS f0))
(VAR A)
(RULES
  f0(A) -> f3(0)
  f3(A) -> f3(A + 1) [ A >= 0 /\ 41 >= A ]
  f3(A) -> f3(A + 1) [ A >= 0 /\ 41 >= A /\ 0 >= B + 1 ]
  f3(A) -> f13(A)    [ A >= 0 /\ A >= 42 ]
)
```

Constants are abstracted to `K` in `piacc`. The resulting dependencies on tick are `[ tick ~+> tick, K ~^> tick ]`. 
We infer `PRIMREC` due to `K ~^> tick`. Actually `tick` and `K` are implicitly constant, thus the result should be constant.


### Example: _resets_

Following example is constant, but `paicc` infers `MAYBE`. 

```
(COMMENT Brockschmidt_16/SAS10/nd_loop.koat-ai)
(GOAL COMPLEXITY)
(STARTTERM (FUNCTIONSYMBOLS start0))
(VAR A B C D)
(RULES
  start(A, B, C, D)  -> lbl51(E, B, 0, D) [ C - D >= 0 /\ -C + D >= 0 /\ A - B >= 0 /\ -A + B >= 0 /\ A = B /\ C = D ]
  lbl51(A, B, C, D)  -> stop(A, B, C, D) [ C >= 0 /\ C >= A /\ 9 >= C ]
  lbl51(A, B, C, D)  -> stop(A, B, C, D) [ C >= 0 /\ A >= C + 3 /\ 9 >= C ]
  lbl51(A, B, C, D)  -> cut(A, B, C, D) [ C >= 0 /\ A >= C + 1 /\ C + 2 >= A /\ 9 >= A /\ 9 >= C ]
  lbl51(A, B, C, D)  -> stop(A, B, C, D) [ C >= 0 /\ A >= 10 /\ A >= C + 1 /\ C + 2 >= A /\ 9 >= C ]
  cut(A, B, C, D)    -> lbl51(E, B, A, D) [ -C + 8 >= 0 /\ A - C - 1 >= 0 /\ -A - C + 17 >= 0 /\ C >= 0 /\ A + C - 1 >= 0 /\ -A + C + 2 >= 0 /\ -A + 9 >= 0 /\ A - 1 >= 0 /\ C + 2 >= A /\ 9 >= A /\ A >= C + 1 ]
  start0(A, B, C, D) -> start(B, B, D, D)
)
```

The inner loop `lb51 ~> cut ~> lb51` depends on `C`. Though `C` is initialised with `0`. Resets are not supported.

Other examples depending on resets: `Flores-Montoya_16/easy1.c.koat`.


### Example: _local growth_

No local growth is inferred. Should work?

```
(GOAL COMPLEXITY)
(STARTTERM (FUNCTIONSYMBOLS start))
(VAR A B)
(RULES
  start(A) -> Com_1(a(A)) :|: A >= 1
  start(A) -> Com_1(a(A)) :|: A >= 2
  start(A) -> Com_1(a(A)) :|: A >= 4
  a(A) -> Com_1(a(B)) :|: 2*B >= 2 && A = 2*B
  a(A) -> Com_1(a(B)) :|: 2*B >= 1 && A = 2*B + 1
)
```

### Example _ambiguous bounds_

Bounds can be ambigious. Consider following rule of example `Brockschmidt_16/c-examples/WTC/sipma91.koat`:

```
evalsipma91bb5in(A,B,C,D)    -> evalsipma91bb8in(A,B,-10 + B,-1 + A)  [-101 + B >= 0 && -103 + A + B >= 0 && -2 + A >= 0 && 110 >= B]
```

With different strategies we infer `B' <= A+B` or `B' <= 110K`. Another common example is of following form `A' <= 2*B` and `A' <= B + C`.
So even if bounds are minimised (eg using sum of constants) different templates have to be used.


### Example _rule graph_

Following example is shown to be constant. Besides its name it actually does terminate.
For inferring the loop structure we use the rule graph representation which shows that rule `f4(A) -> f4(1)` is not a loop, thus part of the root of the loop structure.

```
(COMMENT Brockschmidt_16/T2/loop_on_input.koat)
(GOAL COMPLEXITY)
(STARTTERM (FUNCTIONSYMBOLS f0))
(VAR A B)
(RULES
  f0(A) -> f4(B)
  f4(A) -> f4(1)     :|: 0 >= A && 3 >= A
  f4(A) -> f4(A + 1) :|: 3 >= A && A >= 1
  f4(A) -> f12(A)    :|: A >= 4
)
```


### Remarks

Ambiguity of growth is a problem. In cf KoAT there is more interaction between inferred bounds thus also more dependendencies.
LARE uses separate abstraction steps. Here it is difficult to use existing information as for example unbound variables.

