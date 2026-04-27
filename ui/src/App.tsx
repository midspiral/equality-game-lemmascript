import { useState } from "react";
import {
  type Expr,
  type Op,
  evalExpr,
  leaves,
  canEqualize,
} from "../../src/equality";

type Item = { id: string; expr: Expr };
type SideId = "L" | "R";
type SideState = { items: Item[] };
type Selection = { side: SideId; first?: string; second?: string };
type Status =
  | { kind: "playing" }
  | { kind: "won"; reason: string }
  | { kind: "lost"; reason: string }
  | { kind: "continuing"; reason: string };

const OPS: { op: Op; sym: string; aria: string }[] = [
  { op: "Add", sym: "+", aria: "plus" },
  { op: "Sub", sym: "−", aria: "minus" },
  { op: "Mul", sym: "×", aria: "times" },
  { op: "Div", sym: "÷", aria: "divide" },
];

let _id = 0;
const nextId = () => `i${++_id}`;
const dealDigit = () => 1 + Math.floor(Math.random() * 9);
const card = (v: number): Item => ({ id: nextId(), expr: { kind: "num", v } });

function rawDigits(items: Item[]): number[] {
  const acc: number[] = [];
  for (const it of items) acc.push(...leaves(it.expr));
  return acc;
}

function parseBoardHash(): { left: number[]; right: number[] } | null {
  const h = decodeURIComponent(window.location.hash.slice(1));
  if (!h) return null;
  const [lStr, rStr] = h.split("|");
  if (!lStr || !rStr) return null;
  const parse = (s: string) =>
    s.split(",").map(Number).filter((n) => n >= 1 && n <= 9 && Number.isInteger(n));
  const left = parse(lStr);
  const right = parse(rStr);
  if (left.length === 0 || right.length === 0) return null;
  if (left.length !== lStr.split(",").length || right.length !== rStr.split(",").length)
    return null;
  return { left, right };
}

function makeBoardHash(leftItems: Item[], rightItems: Item[]): string {
  const L = rawDigits(leftItems).join(",");
  const R = rawDigits(rightItems).join(",");
  return `${L}|${R}`;
}

function exprText(e: Expr): string {
  if (e.kind === "num") return String(e.v);
  const s = OPS.find((o) => o.op === e.op)!.sym;
  return `(${exprText(e.l)} ${s} ${exprText(e.r)})`;
}

function exprValue(e: Expr): number | null {
  const r = evalExpr(e);
  return r.kind === "ok" ? r.v : null;
}

function multisetEqual(a: number[], b: number[]): boolean {
  if (a.length !== b.length) return false;
  const counts = new Map<number, number>();
  for (const x of a) counts.set(x, (counts.get(x) ?? 0) + 1);
  for (const x of b) {
    const c = counts.get(x);
    if (!c) return false;
    counts.set(x, c - 1);
  }
  return true;
}

type Snapshot = { left: SideState; right: SideState };

function initSide(digits?: number[]): SideState {
  return { items: (digits ?? [dealDigit()]).map((d) => card(d)) };
}

const initBoard = parseBoardHash();

export function App() {
  const [left, setLeft] = useState<SideState>(initSide(initBoard?.left));
  const [right, setRight] = useState<SideState>(initSide(initBoard?.right));
  const [history, setHistory] = useState<Snapshot[]>([]);
  const [sel, setSel] = useState<Selection | null>(null);
  const [status, setStatus] = useState<Status>({ kind: "playing" });
  const [round, setRound] = useState(1);
  const [wins, setWins] = useState(0);
  const [copied, setCopied] = useState(false);

  const setSide = (s: SideId) => (s === "L" ? setLeft : setRight);
  const sideState = (s: SideId) => (s === "L" ? left : right);

  const playAgain = () => {
    setLeft({ items: [card(dealDigit())] });
    setRight({ items: [card(dealDigit())] });
    setHistory([]);
    setSel(null);
    setStatus({ kind: "playing" });
    setRound(1);
    window.history.replaceState(null, "", window.location.pathname);
  };

  const share = () => {
    const hash = makeBoardHash(left.items, right.items);
    window.location.hash = hash;
    navigator.clipboard.writeText(window.location.href).then(() => {
      setCopied(true);
      setTimeout(() => setCopied(false), 1500);
    });
  };

  const dealMore = () => {
    setLeft((s) => ({ items: [...s.items, card(dealDigit())] }));
    setRight((s) => ({ items: [...s.items, card(dealDigit())] }));
    setHistory([]);
    setSel(null);
    setStatus({ kind: "playing" });
    setRound((r) => r + 1);
  };

  const undo = () => {
    if (history.length === 0) return;
    const prev = history[history.length - 1];
    setLeft(prev.left);
    setRight(prev.right);
    setHistory((h) => h.slice(0, -1));
    setSel(null);
    setStatus({ kind: "playing" });
  };

  const onItemClick = (side: SideId, id: string) => {
    if (status.kind !== "playing") return;
    if (!sel || sel.side !== side) {
      setSel({ side, first: id });
      return;
    }
    if (sel.first === id) {
      setSel(null);
      return;
    }
    if (sel.first && !sel.second) {
      setSel({ ...sel, second: id });
      return;
    }
    setSel({ side, first: id });
  };

  const onOpClick = (op: Op) => {
    if (!sel || !sel.first || !sel.second) return;
    const side = sel.side;
    const state = sideState(side);
    const a = state.items.find((it) => it.id === sel.first);
    const b = state.items.find((it) => it.id === sel.second);
    if (!a || !b) return;
    const merged: Expr = { kind: "app", op, l: a.expr, r: b.expr };
    const r = evalExpr(merged);
    if (r.kind === "err") {
      setStatus({
        kind: "playing",
      });
      return;
    }
    const newItem: Item = { id: nextId(), expr: merged };
    setHistory((h) => [...h, { left, right }]);
    setSide(side)({
      items: state.items
        .filter((it) => it.id !== a.id && it.id !== b.id)
        .concat(newItem),
    });
    setSel(null);
  };

  const claimEqual = () => {
    if (left.items.length !== 1 || right.items.length !== 1) {
      setStatus({
        kind: "lost",
        reason: "Combine each side down to one expression first.",
      });
      return;
    }
    const lv = exprValue(left.items[0].expr);
    const rv = exprValue(right.items[0].expr);
    if (lv === null || rv === null) {
      setStatus({ kind: "lost", reason: "Expression doesn't evaluate." });
      return;
    }
    if (lv === rv) {
      setWins((w) => w + 1);
      setStatus({
        kind: "won",
        reason: `Both sides evaluate to ${lv}. ✓`,
      });
    } else {
      setStatus({
        kind: "lost",
        reason: `Left = ${lv}, right = ${rv}. Not equal.`,
      });
    }
  };

  const claimImpossible = () => {
    const L = rawDigits(left.items);
    const R = rawDigits(right.items);
    if (canEqualize(L, R)) {
      setStatus({
        kind: "lost",
        reason: "Equality IS possible — system found a match.",
      });
    } else {
      setWins((w) => w + 1);
      setStatus({
        kind: "continuing",
        reason: "Correct — no equality possible. Dealing more cards…",
      });
      setTimeout(dealMore, 800);
    }
  };

  return (
    <div className="min-h-screen bg-slate-50 text-slate-900 p-6 font-sans">
      <header className="max-w-4xl mx-auto mb-6 flex items-baseline justify-between">
        <h1 className="text-3xl font-bold tracking-tight text-slate-900">Equality</h1>
        <div className="text-sm text-slate-500">
          Round {round} · Wins {wins}
        </div>
      </header>

      <main className="max-w-4xl mx-auto space-y-6">
        <div className="grid grid-cols-2 gap-4">
          <Side
            id="L"
            label="Left"
            state={left}
            sel={sel}
            onItemClick={onItemClick}
            disabled={status.kind !== "playing"}
          />
          <Side
            id="R"
            label="Right"
            state={right}
            sel={sel}
            onItemClick={onItemClick}
            disabled={status.kind !== "playing"}
          />
        </div>

        <OpRow
          enabled={!!sel?.first && !!sel?.second && status.kind === "playing"}
          onOp={onOpClick}
        />

        <div className="flex flex-wrap gap-3 justify-center pt-2">
          <Button
            onClick={claimEqual}
            disabled={status.kind !== "playing"}
            tone="primary"
          >
            Claim equal
          </Button>
          <Button
            onClick={claimImpossible}
            disabled={status.kind !== "playing"}
            tone="warn"
          >
            Claim impossible
          </Button>
          <Button
            onClick={undo}
            disabled={history.length === 0 || status.kind !== "playing"}
            tone="ghost"
          >
            Undo
          </Button>
          <Button onClick={share} tone="ghost">
            {copied ? "Copied!" : "Share"}
          </Button>
        </div>

        {status.kind !== "playing" && (
          <Banner
            status={status}
            onPlayAgain={playAgain}
            onResume={() => setStatus({ kind: "playing" })}
          />
        )}

        <Help />
      </main>

      <footer className="max-w-4xl mx-auto mt-10 pb-4 flex items-center justify-center gap-3 text-xs text-slate-500">
        <span>
          Verified with{" "}
          <a
            href="https://github.com/midspiral/LemmaScript"
            target="_blank"
            rel="noreferrer"
            className="text-slate-600 underline decoration-slate-300 underline-offset-2 hover:text-indigo-600 hover:decoration-indigo-400 transition"
          >
            LemmaScript
          </a>
        </span>
        <span aria-hidden className="text-slate-300">·</span>
        <a
          href="https://github.com/midspiral/equality-game-lemmascript"
          target="_blank"
          rel="noreferrer"
          className="text-slate-600 underline decoration-slate-300 underline-offset-2 hover:text-indigo-600 hover:decoration-indigo-400 transition"
        >
          Source
        </a>
      </footer>
    </div>
  );
}

function Side(props: {
  id: SideId;
  label: string;
  state: SideState;
  sel: Selection | null;
  onItemClick: (side: SideId, id: string) => void;
  disabled: boolean;
}) {
  const { id, label, state, sel, onItemClick, disabled } = props;
  const sumValue = state.items.length === 1 ? exprValue(state.items[0].expr) : null;
  return (
    <section className="rounded-2xl bg-white ring-1 ring-slate-200 shadow-sm p-4 min-h-[180px]">
      <div className="flex items-center justify-between mb-3">
        <h2 className="text-lg font-semibold text-slate-700">{label}</h2>
        {sumValue !== null && (
          <div className="text-sm font-mono text-emerald-700 bg-emerald-50 px-2 py-0.5 rounded">
            = {sumValue}
          </div>
        )}
      </div>
      <div className="flex flex-wrap gap-2">
        {state.items.map((it) => (
          <ItemChip
            key={it.id}
            item={it}
            badge={
              sel?.side === id && sel.first === it.id
                ? 1
                : sel?.side === id && sel.second === it.id
                  ? 2
                  : null
            }
            onClick={() => !disabled && onItemClick(id, it.id)}
          />
        ))}
      </div>
    </section>
  );
}

function ItemChip(props: {
  item: Item;
  badge: 1 | 2 | null;
  onClick: () => void;
}) {
  const { item, badge, onClick } = props;
  const isLeaf = item.expr.kind === "num";
  const v = exprValue(item.expr);
  const selected = badge !== null;
  return (
    <button
      onClick={onClick}
      className={`relative px-3 py-2 rounded-xl font-mono text-base transition
        ${
          selected
            ? "bg-indigo-600 text-white ring-2 ring-indigo-300 shadow"
            : isLeaf
              ? "bg-slate-100 text-slate-900 hover:bg-slate-200 ring-1 ring-slate-200"
              : "bg-indigo-50 text-slate-800 hover:bg-indigo-100 ring-1 ring-indigo-200"
        }`}
    >
      {badge && (
        <span className="absolute -top-2 -left-2 w-5 h-5 rounded-full bg-amber-400 text-slate-900 text-xs font-bold flex items-center justify-center shadow">
          {badge}
        </span>
      )}
      <span>{exprText(item.expr)}</span>
      {!isLeaf && v !== null && (
        <span
          className={`ml-2 text-xs ${
            selected ? "text-indigo-100" : "text-emerald-700"
          }`}
        >
          ={v}
        </span>
      )}
    </button>
  );
}

function OpRow(props: { enabled: boolean; onOp: (op: Op) => void }) {
  return (
    <div className="flex justify-center gap-2">
      {OPS.map(({ op, sym, aria }) => (
        <button
          key={op}
          aria-label={aria}
          onClick={() => props.onOp(op)}
          disabled={!props.enabled}
          className={`w-12 h-12 rounded-xl text-2xl font-bold transition
            ${
              props.enabled
                ? "bg-amber-400 text-slate-900 hover:bg-amber-300 shadow ring-1 ring-amber-500"
                : "bg-slate-200 text-slate-400 cursor-not-allowed"
            }`}
        >
          {sym}
        </button>
      ))}
    </div>
  );
}

function Button(props: {
  onClick: () => void;
  disabled?: boolean;
  tone: "primary" | "warn" | "ghost";
  children: React.ReactNode;
}) {
  const tones: Record<typeof props.tone, string> = {
    primary: "bg-emerald-600 hover:bg-emerald-500 text-white shadow",
    warn: "bg-rose-500 hover:bg-rose-400 text-white shadow",
    ghost: "bg-white hover:bg-slate-100 text-slate-700 ring-1 ring-slate-300",
  };
  return (
    <button
      onClick={props.onClick}
      disabled={props.disabled}
      className={`px-4 py-2 rounded-lg font-semibold transition
        ${props.disabled ? "opacity-40 cursor-not-allowed" : tones[props.tone]}`}
    >
      {props.children}
    </button>
  );
}

function Banner(props: {
  status: Status;
  onPlayAgain: () => void;
  onResume: () => void;
}) {
  if (props.status.kind === "playing") return null;
  const isPositive =
    props.status.kind === "won" || props.status.kind === "continuing";
  return (
    <div
      className={`rounded-2xl p-4 ring-1 ${
        isPositive
          ? "bg-emerald-50 ring-emerald-200 text-emerald-900"
          : "bg-rose-50 ring-rose-200 text-rose-900"
      }`}
    >
      <div className="font-semibold text-lg mb-1">
        {isPositive ? "✓ Correct" : "✗ Wrong"}
      </div>
      <div className="text-sm mb-3">{props.status.reason}</div>
      {props.status.kind === "lost" && (
        <div className="flex gap-2">
          <Button onClick={props.onResume} tone="primary">
            Resume
          </Button>
          <Button onClick={props.onPlayAgain} tone="ghost">
            Play again
          </Button>
        </div>
      )}
      {props.status.kind === "won" && (
        <Button onClick={props.onPlayAgain} tone="ghost">
          Play again
        </Button>
      )}
    </div>
  );
}

function Help() {
  return (
    <details className="text-sm text-slate-600 max-w-prose mx-auto">
      <summary className="cursor-pointer text-slate-700 font-medium">How to play</summary>
      <ul className="list-disc pl-5 mt-2 space-y-1">
        <li>Each side starts with one card (a digit 1–9).</li>
        <li>
          Click two items on the <em>same</em> side, then click an operator
          (+, −, ×, ÷) to combine them. Order matters: <strong>1</strong> is
          the left operand, <strong>2</strong> is the right.
        </li>
        <li>
          Division must be exact (no remainder, no division by zero).
        </li>
        <li>
          Combine each side down to one expression with the same value, then
          click <strong>Claim equal</strong>.
        </li>
        <li>
          Or click <strong>Claim impossible</strong> if you believe no
          equality exists. The system checks via the verified{" "}
          <code>canEqualize</code> — if you're right, more cards are dealt.
        </li>
      </ul>
    </details>
  );
}
