import Mathlib

namespace Solady.Bytes

open Mathlib

/-
If a `foldl` step pushes exactly one element into an array each time,
the final size is the initial size plus the list length.
-/
theorem foldl_push_size
    {α β : Type} :
    ∀ (xs : List α) (step : Array β → α → β) (out : Array β),
      (List.foldl (fun out x => out.push (step out x)) out xs).size
        = out.size + xs.length := by
  intro xs
  induction xs with
  | nil =>
      intro step out
      simp
  | cons x xs ih =>
      intro step out
      simp [List.foldl_cons, ih, Array.size_push, Nat.add_comm, Nat.add_left_comm]


/-- Little-endian bytes stored in an array. -/
def nat_to_bytes_le (n len : Nat) : Array UInt8 :=
  (List.range len).foldl
    (fun out i => out.push (UInt8.ofNat (n / 256 ^ i % 256)))
    #[]

theorem nat_to_bytes_le_size (n len : Nat) :
    (nat_to_bytes_le n len).size = len := by
  unfold nat_to_bytes_le
  simp

/- Big-endian bytes as a `ByteArray`. -/
def nat_to_bytes_be (n len : Nat) : Array UInt8 :=
  (nat_to_bytes_le n len).reverse

theorem nat_to_bytes_be_size (n len : Nat) :
    (nat_to_bytes_be n len).size = len := by
  unfold nat_to_bytes_be
  simp [Array.size_reverse, nat_to_bytes_le_size]

/-- Convert to ByteArray. -/
def nat_to_bytes_be_to_byte_array (n len : Nat) : ByteArray :=
  { data := (nat_to_bytes_be n len) }

theorem nat_to_bytes_be_to_byte_array_size (n len : Nat) :
    (nat_to_bytes_be_to_byte_array n len).size = len := by
  simp [nat_to_bytes_be_to_byte_array, ByteArray.size, nat_to_bytes_be_size]


/-- Bytes to Nat big-endian. -/
def bytes_to_nat_be (bytes : ByteArray) : Nat :=
  bytes.data.foldl (fun acc byte => acc * 256 + byte.toNat) 0

theorem bytes_to_nat_be_size (bytes : ByteArray) :
    bytes_to_nat_be bytes = bytes.data.foldl (fun acc byte => acc * 256 + byte.toNat) 0 := by
  simp [bytes_to_nat_be]

end Solady.Bytes
