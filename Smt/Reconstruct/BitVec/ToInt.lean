/-
Copyright (c) 2021-2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

@[expose] public section

/-! Lemmas for cvc5's conversions between bit-vectors and integers: the `uf-*` rules of
https://github.com/cvc5/cvc5/blob/main/src/theory/uf/rewrites and `UBV_TO_INT_ELIM`. -/

namespace Smt.Reconstruct.BitVec.ToInt

variable {w : Nat}

theorem uf_bv2nat_int2bv (t : BitVec w) : BitVec.ofInt w (t.toNat : Int) = t := by
  apply BitVec.eq_of_toNat_eq
  simp

theorem uf_bv2nat_int2bv_extend (t : BitVec w) (n : Nat) :
    BitVec.ofInt (n + w) (t.toNat : Int) = BitVec.ofNat n 0 ++ t := by
  apply BitVec.eq_of_toNat_eq
  have h₁ := t.isLt
  have h₂ : 2 ^ w ≤ 2 ^ (n + w) := Nat.pow_le_pow_right (by decide) (Nat.le_add_left w n)
  have h₃ : t.toNat % 2 ^ (n + w) = t.toNat := Nat.mod_eq_of_lt (by omega)
  simp only [BitVec.toNat_ofInt, BitVec.toNat_append, BitVec.toNat_ofNat, Nat.zero_mod,
    Nat.zero_shiftLeft, Nat.zero_or]
  rw [← Int.natCast_emod, Int.toNat_natCast, h₃]

theorem uf_bv2nat_int2bv_extract (t : BitVec w) (m : Nat) :
    BitVec.ofInt (m + 1) (t.toNat : Int) = t.extractLsb m 0 := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.extractLsb, BitVec.extractLsb']

theorem uf_int2bv_bv2nat (i : Int) : ((BitVec.ofInt w i).toNat : Int) = i % 2 ^ w := by
  have : (0 : Int) < 2 ^ w := Int.pow_pos (by decide)
  simp only [BitVec.toNat_ofInt, Int.natCast_pow, Int.cast_ofNat_Int]
  exact Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega))

theorem uf_bv2nat_geq_elim (x : BitVec w) (n : Int) :
    ((x.toNat : Int) ≥ n) =
      (if n ≥ 2 ^ w then False else if n < 0 then True else x ≥ BitVec.ofInt w n) := by
  have hx : ((x.toNat : Nat) : Int) < (2 : Int) ^ w := by
    have := x.isLt; exact_mod_cast this
  split <;> rename_i h₁
  · simp only [eq_iff_iff, iff_false, ge_iff_le, Int.not_le]; omega
  split <;> rename_i h₂
  · simp only [eq_iff_iff, iff_true]; omega
  · simp only [ge_iff_le, BitVec.le_def, BitVec.toNat_ofInt, eq_iff_iff]
    have : n % (2 : Int) ^ w = n := Int.emod_eq_of_lt (by omega) (by omega)
    rw [Int.natCast_pow, Int.cast_ofNat_Int, this, ← Int.ofNat_le, Int.toNat_of_nonneg (by omega)]

theorem uf_int2bv_bvult_equiv (t s : BitVec w) : (t < s) = ((t.toNat : Int) < s.toNat) := by
  simp [BitVec.lt_def]

theorem uf_int2bv_bvule_equiv (t s : BitVec w) : (t ≤ s) = ((t.toNat : Int) ≤ s.toNat) := by
  simp [BitVec.le_def]

theorem extractLsb_self_eq (x : BitVec w) (i b : Nat) (hb : b < 2) :
    (x.extractLsb i i = BitVec.ofNat _ b) = ((x.toNat / 2 ^ i) % 2 = b) := by
  rw [BitVec.toNat_eq]
  simp [BitVec.extractLsb_toNat, Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt hb]

theorem uf_sbv_to_int_elim {m : Nat} (t : BitVec (m + 1)) :
    t.toInt = if t.extractLsb m m = BitVec.ofNat _ 0 then (t.toNat : Int)
      else (t.toNat : Int) - 2 ^ (m + 1) := by
  simp only [extractLsb_self_eq t m 0 (by decide), BitVec.toInt_eq_msb_cond,
    BitVec.msb_eq_getLsbD_last, Nat.add_sub_cancel, BitVec.getLsbD, Nat.testBit,
    Nat.shiftRight_eq_div_pow]
  have := Nat.mod_two_eq_zero_or_one (t.toNat / 2 ^ m)
  split <;> split <;> simp_all <;> omega

/-- `t₀ + ⋯ + tₙ`, associated to the left, where `tᵢ = if x[i:i] = 1 then 2 ^ i else 0`. -/
def bitSum (x : BitVec w) : Nat → Int
  | 0 => if x.extractLsb 0 0 = BitVec.ofNat _ 1 then 1 else 0
  | n + 1 => bitSum x n + if x.extractLsb (n + 1) (n + 1) = BitVec.ofNat _ 1 then 2 ^ (n + 1) else 0

theorem bitSum_eq (x : BitVec w) (n : Nat) : bitSum x n = ((x.toNat % 2 ^ (n + 1) : Nat) : Int) := by
  induction n with
  | zero =>
    simp only [bitSum, extractLsb_self_eq x 0 1 (by decide)]
    have := Nat.mod_two_eq_zero_or_one x.toNat
    split <;> simp_all
  | succ n ih =>
    simp only [bitSum, ih, extractLsb_self_eq x (n + 1) 1 (by decide)]
    rw [Nat.mod_pow_succ (b := 2) (k := n + 1)]
    have := Nat.mod_two_eq_zero_or_one (x.toNat / 2 ^ (n + 1))
    split <;> simp_all [Int.natCast_add, Int.natCast_pow]

theorem ubv_to_int_elim {m : Nat} (x : BitVec (m + 1)) : (x.toNat : Int) = bitSum x m := by
  rw [bitSum_eq, Nat.mod_eq_of_lt x.isLt]

end Smt.Reconstruct.BitVec.ToInt
