import Mathlib.Tactic
import Commonplace.Nat
import Commonplace.Fibonacci

-- ANCHOR: fibs_filter
def even_fibs' (i : Nat) : List Nat := (Fibs i).filter (· % 2 == 0)

#eval (even_fibs' 33).sum -- 4613732
-- ANCHOR_END: fibs_filter

theorem even_fibs'_is_even (i : Nat) : ∀ x ∈ even_fibs' i, Even x := by
  apply even_filter

-- ANCHOR: fibs_even_example
#eval FibsEven 7 -- [2, 8, 34, 144, 610, 2584, 10946, 46368]
#eval even_fibs' 7 -- [2, 8, 34, 144, 610, 2584, 10946, 46368]

example : even_fibs' 2  = FibsEven 0 := by rfl
example : even_fibs' 5  = FibsEven 1 := by rfl
example : even_fibs' 8  = FibsEven 2 := by rfl
example : even_fibs' 11 = FibsEven 3 := by rfl
-- ANCHOR_END: fibs_even_example

-- ANCHOR: even_fibs_eq_map_proof
theorem even_fibs'_eq_map (i : Nat) :
  even_fibs' (i * 3 + 2) = (List.range' 2 (i + 1) 3 |> List.map Fibs.nth) := by
  unfold even_fibs'
  rw [Fibs.nth_map_eq, List.filter_map]
  have : (fun x ↦ x % 2 == 0) ∘ Fibs.nth = (fun x ↦ (Fibs.nth x % 2) == 0) := by rfl
  rw [this]; clear this
  apply congrArg
  induction i with
  | zero =>
    simp;
    repeat unfold List.range; repeat (unfold List.range.loop; simp)
  | succ i' hi =>
    have : (i' + 1) * 3 + 2 + 1 = i' * 3 + 2 + 1 + 3 := by ring
    rw [this]; clear this
    rw [List.range_add, List.filter_append, hi]
    simp [List.range_succ, List.filter_cons, mod_2_even.eq]
    have : i' * 3 + 2 + 1 + 2 = (i' + 1) * 3 + 2 := by ring
    simp [ this
         , Fibs.even_for_3_mul
         , Nat.not_even_iff_odd.mpr (Fibs.odd_for_3_mul_add_1 i')
         , Nat.not_even_iff_odd.mpr (Fibs.odd_for_3_mul_add_2 i')
         ]
    rw [Nat.add_comm (m:=2), Nat.mul_comm, ← List.range'_concat]
-- ANCHOR_END: even_fibs_eq_map_proof

theorem length_even_fibs' {i : Nat} : (even_fibs' (i * 3 + 2)).length = i + 1 := by
  rw [even_fibs'_eq_map, List.length_map, List.length_range']

-- ANCHOR: even_fibs_eq_fibseven
theorem even_fibs'_eq_fibseven {i : Nat} : even_fibs' (i * 3 + 2) = FibsEven i := by
  rw [even_fibs'_eq_map]
  induction i with
  | zero => simp
  | succ i' hi =>
    rw [List.range'_concat, List.map_append, FibsEven.succ_eq, hi]
    simp
    have : 2 + 3 * (i' + 1) = (i' + 1) * 3 + 2 := by ring
    rw [this, FibsEven.as_fibs]
-- ANCHOR_END: even_fibs_eq_fibseven

-- ANCHOR: even_sum_sequence_eval
#eval (List.range 7).map (λ n ↦ (FibsEven n).sum)  -- [2, 10, 44, 188, 798, 3382, 14328]
-- ANCHOR_END: even_sum_sequence_eval

-- ANCHOR: even_sum_sequence_eval_2
#eval (List.range 7).map (λ n ↦ Fibs.nth (3 * n + 4) / 2)  -- [2, 10, 44, 188, 798, 3382, 14328]
-- ANCHOR_END: even_sum_sequence_eval_2

-- ANCHOR: even_fib_sum_eq_fibs_nth
theorem even_fibs'_sum {i : Nat} :
  (even_fibs' (i * 3 + 2)).sum = Fibs.nth (3 * i + 4) / 2 := by
  rw [even_fibs'_eq_fibseven]
  apply FibsEven.sum_eq
-- ANCHOR_END: even_fib_sum_eq_fibs_nth
