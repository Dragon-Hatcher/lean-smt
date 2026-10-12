import Smt

-- The comparison eliminations `bv-ule-eliminate`, `bv-ugt-eliminate`,
-- `bv-uge-eliminate` and `bv-sle-eliminate`: no goal is left over.

example (f : Int → BitVec 8) (i : Int) : f i ≤ 127#8 → ¬ (127#8 < f i) := by
  smt

example (x y : BitVec 8) : x > y → y < x := by
  smt

example (x y : BitVec 8) : x ≥ y → y ≤ x := by
  smt

example (x y : BitVec 8) : x.sle y → ¬ y.slt x := by
  smt
