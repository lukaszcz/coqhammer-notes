# Evaluating CoqHammer with CoqGym

CoqHammer can be evaluated using CoqGym machinery, but not from CoqGym's serialized proof-state data alone. CoqHammer needs a live Coq/Rocq environment because premise selection, translation, ATP invocation, and reconstruction all depend on the current environment, evar map, accessible constants, local hypotheses, and tactic execution.

The practical approach is to use CoqGym's source-level replay/evaluation infrastructure: replay project proofs in Coq, pause at selected proof states, run CoqHammer as an ordinary tactic, record the result, roll back, and continue replaying the original proof.

## Recommended evaluation protocol

At each chosen replay point:

1. Save or remember the current Coq/SerAPI state.
2. Run CoqHammer, for example:

   ```coq
   From Hammer Require Import Hammer.
   Set Hammer ATPLimit 10.
   Set Hammer ReconstrLimit 5.
   hammer.
   ```

3. Check whether the tactic solved the goal or all remaining goals, depending on the benchmark definition.
4. Record success/failure, runtime, and diagnostic output.
5. Roll back to the saved state.
6. Continue replaying the original proof.

For tactics-only evaluation, use CoqHammer tactics such as `sauto`, `hauto`, or related tactics instead of full `hammer`. This avoids ATP dependencies and measures proof-search/reconstruction rather than the full premise-selection/ATP pipeline.

## Possible benchmark modes

### Initial-goal mode

Try `hammer` immediately after `Proof.`. This measures fully automatic theorem proving from the theorem statement. It is close to the existing in-repo CoqHammer evaluation harness, which inserts `hammer_hook` at proof starts.

### Intermediate-state mode

Replay human proofs and try `hammer` at intermediate proof states. This is a natural CoqGym-style evaluation and may be closer to realistic interactive use, since users often do some setup manually before calling `hammer`, e.g. after `intros`, `destruct`, `induction`, or simplification.

### Earliest-success mode

For each theorem, replay the proof and find the earliest proof state from which `hammer` can finish. This measures how much of the human proof could have been replaced by CoqHammer.

### Tactics-only mode

Run `sauto`, `hauto`, etc. at replayed states. This is cheaper and more reproducible than full `hammer`, but it does not evaluate ATP premise selection and external prover integration.

## Requirements and caveats

- Use a CoqHammer branch compatible with the Coq version used by the CoqGym project.
- Install CoqHammer and its dependencies in the same environment used for replay.
- Full `hammer` requires external ATPs on `PATH` unless the experiment intentionally disables them.
- Running `hammer` at every proof state can be very expensive; start with one project, short time limits, and a restricted prover set.
- Define success precisely: solving the focused goal, solving all current goals, or completing the theorem.
- For clean measurements, use careful SerAPI rollback or fresh Coq processes. Calling `Hammer_cleanup.` between attempts may help clear CoqHammer caches.

## Relation to the in-repo `eval/` harness

The in-repo `eval/` harness mutates Coq source files by inserting `hammer_hook` near proof starts, then recompiles the library to generate ATP problems, run provers, and reconstruct proofs. CoqGym can bypass this harness by invoking `hammer` directly during proof replay.

Thus:

- use `eval/` if you want CoqHammer's historical ATP-generation/reconstruction/statistics pipeline;
- use CoqGym replay if you want a proof-state benchmark of CoqHammer as a tactic at initial or intermediate states.
