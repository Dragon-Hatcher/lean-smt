import Smt

-- `ubv_to_int`, `sbv_to_int` and `int_to_bv`.

theorem conversions_show (x : BitVec 8) (i : Int) :
    (x.toNat : Int) + x.toInt = i → BitVec.ofInt 8 i = x := by
  smt_show
  sorry

example (x : BitVec 8) : Int.ofNat x.toNat < 256 := by
  smt

example (x : BitVec 8) : (x.toNat : Int) ≥ 0 := by
  smt

example (x : BitVec 4) : (x.toNat : Int) ≤ 15 := by
  smt

example (x : BitVec 8) (f : BitVec 8 → Prop) (h : f (BitVec.ofInt 8 (x.toNat : Int))) : f x := by
  smt [h]

-- The shapes cvc5 gives `UBV_TO_INT_ELIM` and `uf-sbv-to-int-elim`.

open Smt.Reconstruct.BitVec.ToInt in
example (x : BitVec 4) : (x.toNat : Int) =
    (((if BitVec.extractLsb 0 0 x = 1#1 then 1 else 0) + if BitVec.extractLsb 1 1 x = 1#1 then 2 else 0) +
      if BitVec.extractLsb 2 2 x = 1#1 then 4 else 0) +
    if BitVec.extractLsb 3 3 x = 1#1 then 8 else 0 :=
  ubv_to_int_elim x

open Smt.Reconstruct.BitVec.ToInt in
example (x : BitVec 8) :
    x.toInt = if BitVec.extractLsb 7 7 x = 0#1 then (x.toNat : Int) else (x.toNat : Int) - 256 :=
  uf_sbv_to_int_elim x
