# Equality

A small two-player card game where the verified core decides — with full
soundness and completeness — whether the dealt digits can be combined into
equal expressions on each side.

Built with [LemmaScript](https://github.com/midspiral/LemmaScript): a single
TypeScript module is annotated with `//@` specs and translated to Dafny, where
the soundness/completeness theorems are mechanically proved. The same module
runs in the React UI.

Play the game here: [https://midspiral.github.io/equality-game-lemmascript/](https://midspiral.github.io/equality-game-lemmascript/).

## Game

Each side accumulates a sequence of digits (1–9). On each turn the player can:

- **Combine** two items on the same side using `+`, `−`, `×`, or `÷` (division
  only when exact — no remainder, no division by zero). Order matters: the
  first item picked is the left operand. Each combination collapses two items
  into one bracketed sub-expression.
- **Claim equal** when each side has been collapsed to a single expression and
  the values match.
- **Claim impossible** when no combination of operations on the dealt digits
  could ever make the two sides equal.

The system adjudicates both claims using the verified core. A correct
"impossible" deals more cards; a correct "equal" wins the round.

## What is verified

The verification target is `src/equality.ts`. The Dafny output
(`src/equality.dfy`) carries every proof. The whole module verifies in
**753 verification conditions, 0 errors, 0 `assume`s, 0 axioms** —
all proofs are complete, with no escape hatches.

```sh
npx tsx ../LemmaScript/tools/src/lsc.ts check --backend=dafny \
  --time-limit=180 --extra-flags="--isolate-assertions" src/equality.ts
```

### The contract

The two top-level theorems are stated as method postconditions. Both quantify
over the existential predicate `ReachableExists`, which captures the *meaning*
of "value `v` is reachable from `cards`":

```dafny
ghost predicate ReachableExists(cards: seq<int>, v: int)
{
  exists e: Expr ::
    evalExpr(e) == ok(v) && multiset(leaves(e)) == multiset(cards)
}
```

That is: there is some expression tree `e` whose leaves are exactly the
multiset of `cards` (in any order, since the player may reorder) and whose
evaluation yields `v` (or `err` for invalid divisions, which is excluded by
`evalExpr(e) == ok(v)`).

#### Theorem 1 — `reachable` is sound and complete

```dafny
method reachable(cards: seq<int>) returns (res: set<int>)
  requires |cards| >= 1
  ensures forall v :: v in res ==> ReachableExists(cards, v)        // soundness
  ensures forall v :: ReachableExists(cards, v) ==> v in res        // completeness
  decreases |cards|
```

`reachable(cards)` returns *exactly* the set of values that can be produced by
any expression tree whose leaves match `cards` as a multiset. Nothing is
missed; nothing is fabricated.

#### Theorem 2 — `canEqualize` decides the game faithfully

```dafny
ghost predicate ExpressionsAgree(L: seq<int>, R: seq<int>)
{
  exists eL: Expr, eR: Expr ::
    multiset(leaves(eL)) == multiset(L) &&
    multiset(leaves(eR)) == multiset(R) &&
    evalExpr(eL).ok? && evalExpr(eR).ok? &&
    evalExpr(eL).v == evalExpr(eR).v
}

method canEqualize(L: seq<int>, R: seq<int>) returns (res: bool)
  requires |L| >= 1 && |R| >= 1
  ensures res <==> ExpressionsAgree(L, R)
```

`canEqualize(L, R)` is `true` exactly when there exists *some* pair of
expressions, one per side, that evaluate to the same value using each side's
dealt digits as a multiset. So a game-impossible position produces `false`,
and a game-possible position produces `true` — both with mathematical
certainty.

### Proof structure

The proofs of Theorem 1 dominate; Theorem 2 falls out of Theorem 1 in a few
forall blocks. The chain of supporting lemmas:

#### Bit arithmetic

The algorithm enumerates subsets of card positions via a bitmask `m ∈
[1, 2^n − 1)`. Three properties are needed:

- **`Pow2Pos`** — `Pow2(n) ≥ 1` for `n ≥ 0`.
- **`PopCountBounds`** — `0 ≤ PopCount(mask, n) ≤ n`.
- **`PopCountLower`** — `mask ≥ 1 ∧ mask < Pow2(n) ⇒ PopCount(mask, n) ≥ 1`
  (at least one set bit in the relevant range).
- **`PopCountUpper`** — `mask < Pow2(n) − 1 ⇒ PopCount(mask, n) < n`
  (at least one clear bit). This needs:
  - **`Pow2Add`** — `Pow2(a + b) = Pow2(a) · Pow2(b)`.
  - **`PopCountUnchangedSubtract`** — subtracting `Pow2(k)` from a mask leaves
    bits below `k` unchanged. Proved via `BitUnchangedAfterSubtract` and a
    parity helper `SubtractEvenParity`.

These together guarantee that for every iterated mask, the resulting `left`
and `right` sequences are both non-empty and strictly shorter than `cards` —
discharging the recursive call's preconditions and termination measure.

The one place where Dafny's nonlinear int arithmetic needed a stdlib hand-off:

- **`DivByMulPlusRem`** — `(d·k + r) / d == k` when `0 ≤ r < d`. Proved by a
  single call to `Std.Arithmetic.DivMod.LemmaFundamentalDivModConverse`.
- **`DivBy2ThenPow2`** — `(mask / 2) / Pow2(i−1) == mask / Pow2(i)`. Uses
  `Std.Arithmetic.DivMod.LemmaDivDenominator`.

These two stdlib calls are the only "external" pieces; everything else is
proved from first principles in `equality.dfy`.

#### Connecting the imperative loop to a pure split

The body of `reachable` builds `left` and `right` imperatively by checking each
bit. To reason about it, two pure functions mirror the construction:

```dafny
function splitLeft(cards: seq<int>, mask: int): seq<int>
function splitRight(cards: seq<int>, mask: int): seq<int>
```

The lemmas

- **`SplitLeftExtend`** / **`SplitRightExtend`** — appending `cards[i]` to
  `splitLeft(cards[..i], mask)` exactly when bit `i` is set yields
  `splitLeft(cards[..i+1], mask)`,

let the inner i-loop carry the invariants `left == splitLeft(cards[..i],
mask)` and `right == splitRight(cards[..i], mask)`. After the loop:
`left == splitLeft(cards, mask)` and `right == splitRight(cards, mask)`.

#### Soundness

A loop invariant `forall v in out :: ReachableExists(cards, v)` is maintained
through all four nested loops. The witness construction lemma

```dafny
lemma WitnessCombine(L, R, cards, a, b)
  requires multiset(L) + multiset(R) == multiset(cards)
  requires ReachableExists(L, a) && ReachableExists(R, b)
  ensures ReachableExists(cards, a + b)
  ensures ReachableExists(cards, a - b)
  ensures ReachableExists(cards, a * b)
  ensures (b != 0 && a % b == 0) ==> ReachableExists(cards, JSFloorDiv(a, b))
```

extracts existential witnesses `eL` and `eR` from the recursive calls' ensures
(via `:|`), assembles the combined `app(op, eL, eR)`, and proves its leaves
multiset matches `cards`.

The singleton case (`|cards| == 1`) needs a small structural lemma —
**`SingletonExpr`**: any `e` with `multiset(leaves(e)) == multiset([x])` must
be `num(x)`, proved by induction using **`LeavesNonEmpty`** to rule out the
`app` case.

#### Completeness

The harder direction. The claim: every expression `e` with `multiset(leaves(e))
== multiset(cards)` and `evalExpr(e).ok?` has its value in `out` after the
loop. The proof has two parts.

**Combinatorial witness — `ChooseMask`.** Given a target sub-multiset `M1` of
`multiset(cards)`, construct a bitmask `m` such that `splitLeft(cards, m)` has
multiset exactly `M1`:

```dafny
function ChooseMask(cards: seq<int>, M1: multiset<int>): int
```

Proved correct by:

- **`ChooseMaskCorrect`** — `multiset(splitLeft(cards, ChooseMask(cards, M1))) == M1`
  when `M1 ≤ multiset(cards)`.
- **`ChooseMaskBounds`** — `0 ≤ ChooseMask(cards, M1) < Pow2(|cards|)`.
- **`ChooseMaskNonzero`** — when `M1` is non-empty, `ChooseMask(cards, M1) ≥ 1`.
- **`ChooseMaskNotAllOnes`** — when `multiset(cards) − M1` is non-empty,
  `ChooseMask(cards, M1) < Pow2(|cards|) − 1`.

Together: for any non-trivial multiset partition of `multiset(cards)`, some
mask in `[1, Pow2(|cards|) − 1)` realizes it — exactly the range the outer
loop iterates.

**Mask-level coverage invariant.** A ghost predicate

```dafny
ghost predicate MaskCovered(cards: seq<int>, m: int, out: set<int>)
{
  forall op, eL, eR ::
    multiset(leaves(eL)) == multiset(splitLeft(cards, m)) &&
    multiset(leaves(eR)) == multiset(splitRight(cards, m)) &&
    evalExpr(eL).ok? && evalExpr(eR).ok? &&
    opValid(op, evalExpr(eL).v, evalExpr(eR).v)
    ==> applyOp(op, evalExpr(eL).v, evalExpr(eR).v) in out
}
```

is added as an outer-loop invariant: `forall m :: 1 ≤ m < mask ==>
MaskCovered(cards, m, out)`. Maintenance threads through the cross-product
loops via two finer invariants (`PrefixPairsCovered`, `APrefixCovered`) plus
monotonicity lemmas (`MaskCoveredMono`, `AllPrioMasksMono`,
`PrefixPairsCoveredMono`, `APrefixCoveredMono`) that propagate coverage as
`out` grows.

After the outer loop terminates with `mask == Pow2(n) − 1`, every iterated
mask has been covered. The final lemma

- **`CompletenessFromMaskCoverage`** — given `MaskCovered` for all m in
  `[1, Pow2(|cards|) − 1)`, conclude `forall v :: ReachableExists(cards, v) ==>
  v in out`,

is the cap. Given any witness expression `e = app(op, eL, eR)`, it computes
`m := ChooseMask(cards, multiset(leaves(eL)))`, uses the bounds lemmas to
show `1 ≤ m < Pow2(n) − 1`, applies `MaskCovered(cards, m, out)`, and
concludes `evalExpr(e).v in out`. The `num(x)` case is ruled out by the same
multiset-size argument used in singleton completeness.

#### `canEqualize`

Once `reachable` is fully verified, `canEqualize` is short:

- The `true` branch produces a witness `v` in both `reachable(L)` and
  `reachable(R)`. By `reachable`'s soundness, witness expressions exist on
  both sides; they evaluate to the same `v`, so `ExpressionsAgree(L, R)`.
- The `false` branch follows from a loop invariant tracking that every
  element of `i_v_seq` was checked and found absent in `sR`. A `forall`
  block then derives a contradiction from any hypothetical `eL, eR` that
  would witness `ExpressionsAgree`: `reachable`'s completeness places their
  shared value in both `sL` and `sR`, contradicting the loop's exit
  condition.

## Project layout

```
src/
  equality.ts        # the verified module (TypeScript with //@ specs)
  equality.dfy.gen   # auto-generated by lsc — never edited by hand
  equality.dfy       # additions-only proof file, source of truth for Dafny
ui/
  src/App.tsx        # React UI — imports the same equality.ts directly
  ...
LS_TODO.md           # bug reports / fixes contributed back to LemmaScript
```

The TypeScript module is the single source of truth — the React UI imports
`reachable`, `canEqualize`, `evalExpr`, and `leaves` from the same file that
the Dafny backend verifies.

## Running

**Verify:**

```sh
npx tsx ../LemmaScript/tools/src/lsc.ts check --backend=dafny \
  --time-limit=180 --extra-flags="--isolate-assertions" src/equality.ts
```

**UI dev server:**

```sh
cd ui && npm install && npm run dev
```

Open `http://localhost:5173` (or the port Vite picks).

## Acknowledgements

- [LemmaScript](https://github.com/midspiral/LemmaScript) — the verification
  toolchain.
- [Dafny standard library](https://github.com/dafny-lang/dafny/tree/master/Source/DafnyStandardLibraries)
  — `LemmaFundamentalDivModConverse` and `LemmaDivDenominator` from
  `Std.Arithmetic.DivMod`.
