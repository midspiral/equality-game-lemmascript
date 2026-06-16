# Guarantees: src/equality.ts

Generated: 2026-06-16

> Verification is **assumed** (run `lsc check` to discharge the proofs). This report vets only that each `//@ contract` faithfully describes its formal `requires`/`ensures`, via claimcheck's blind round-trip.

## Coverage

- **1** backed contracts: 1 confirmed, 0 disputed
- **0** gaps (contract with no formal spec behind it)

## Claimcheck Results

| Function | Contract | Status |
|----------|----------|--------|
| `canEqualize` | A sound and complete decision procedure for whether the two card lists can be equalized — returns true exactly when expressions over L and R can agree. | ✅ confirmed |

## Confirmed Guarantees

**A sound and complete decision procedure for whether the two card lists can be equalized — returns true exactly when expressions over L and R can agree.** — `canEqualize`
```
canEqualize(L: number[], R: number[]): boolean
  requires L.length >= 1
  requires R.length >= 1
  ensures \result ==> ExpressionsAgree(L, R)
  ensures ExpressionsAgree(L, R) ==> \result
```
- Back-translation: The function canEqualize returns true if and only if the two arrays L and R express the same thing (ExpressionsAgree(L, R) holds).

