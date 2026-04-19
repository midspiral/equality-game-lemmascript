export type Op = "Add" | "Sub" | "Mul" | "Div";

export type Expr =
  | { kind: "num"; v: number }
  | { kind: "app"; op: Op; l: Expr; r: Expr };

export type EvalResult =
  | { kind: "ok"; v: number }
  | { kind: "err" };

export function evalExpr(e: Expr): EvalResult {
  if (e.kind === "num") {
    return { kind: "ok", v: e.v };
  }
  const lr = evalExpr(e.l);
  if (lr.kind === "err") return { kind: "err" };
  const rr = evalExpr(e.r);
  if (rr.kind === "err") return { kind: "err" };
  const a = lr.v;
  const b = rr.v;
  if (e.op === "Add") return { kind: "ok", v: a + b };
  if (e.op === "Sub") return { kind: "ok", v: a - b };
  if (e.op === "Mul") return { kind: "ok", v: a * b };
  if (b === 0) return { kind: "err" };
  if (a % b !== 0) return { kind: "err" };
  return { kind: "ok", v: Math.floor(a / b) };
}

export function leaves(e: Expr): number[] {
  if (e.kind === "num") return [e.v];
  return leaves(e.l).concat(leaves(e.r));
}

export function reachable(cards: number[]): Set<number> {
  //@ requires cards.length >= 1
  //@ decreases cards.length

  const out = new Set<number>();
  if (cards.length === 1) {
    out.add(cards[0]);
    return out;
  }
  const n = cards.length;
  let mask = 1;
  const total = 1 << n;
  while (mask < total - 1) {
    //@ invariant 1 <= mask && mask <= total - 1
    //@ decreases (total - 1) - mask
    const left: number[] = [];
    const right: number[] = [];
    let i = 0;
    while (i < n) {
      //@ invariant 0 <= i && i <= n
      //@ decreases n - i
      if (((mask >> i) & 1) === 1) {
        left.push(cards[i]);
      } else {
        right.push(cards[i]);
      }
      i = i + 1;
    }
    const lvals = reachable(left);
    const rvals = reachable(right);
    for (const a of lvals) {
      for (const b of rvals) {
        out.add(a + b);
        out.add(a - b);
        out.add(a * b);
        if (b !== 0 && a % b === 0) {
          out.add(Math.floor(a / b));
        }
      }
    }
    mask = mask + 1;
  }
  return out;
}

export function canEqualize(L: number[], R: number[]): boolean {
  //@ requires L.length >= 1
  //@ requires R.length >= 1

  const sL = reachable(L);
  const sR = reachable(R);
  for (const v of sL) {
    if (sR.has(v)) return true;
  }
  return false;
}

export type Verdict =
  | { kind: "equal"; eL: Expr; eR: Expr }
  | { kind: "impossible" };
