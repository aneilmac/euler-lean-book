import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic
import Commonplace.List
import Commonplace.Nat

-- ANCHOR: simple_soln
def sum_multiple_3_or_5 (n : Nat) : Nat
  := List.range n
  |> List.filter (λ n ↦ n % 3 == 0 || n % 5 == 0)
  |> List.sum
--- ANCHOR_END: simple_soln

-- ANCHOR: eval_simple_soln
#eval sum_multiple_3_or_5 10   -- Prints 23
#eval sum_multiple_3_or_5 1000 -- Prints 233168
-- ANCHOR_END: eval_simple_soln

-- ANCHOR: better_soln
def sum_divisible_by (t n : Nat) : Nat :=
    let p := (t - 1) / n
    n * (p + 1) * p  / 2

def sum_multiple_3_or_5' (n : Nat) : Nat :=
  let sn := sum_divisible_by n
  sn 3 + sn 5 - sn 15
-- ANCHOR_END: better_soln

-- ANCHOR: eval_better_soln
#eval sum_multiple_3_or_5' 10   -- Prints 23
#eval sum_multiple_3_or_5' 1000 -- Prints 233168
-- ANCHOR_END: eval_better_soln

-- ANCHOR: proof_sum_divisible_by_eq_range_sum
theorem sum_divisible_by_eq_range_sum (n m : Nat):
  sum_divisible_by m n = n * (List.range ((m - 1) / n + 1)).sum := by
  unfold sum_divisible_by
  simp
  rw [ Nat.mul_assoc
     , Nat.mul_div_assoc _ (x_mul_x_succ_dvd_2 _)
     , ← list_range_succ_sum_triangle (n:= (m - 1) / n)
     ]
-- ANCHOR_END: proof_sum_divisible_by_eq_range_sum

-- ANCHOR: sum_divisible_by_eq_range_filter_sum
theorem sum_divisible_by_eq_range_filter_sum (n m : Nat):
  sum_divisible_by m n =
  ((List.range m).filter (· % n == 0)).sum := by
  rw [sum_divisible_by_eq_range_sum]
  by_cases hzn : 0 < n
  case neg =>
    simp at hzn
    simp [hzn, list_filter_eq_nil_sum]
  case pos =>
    induction m with
    | zero => simp
    | succ m' hm =>
      by_cases hzm : 0 < m'
      case neg => simp at hzm; simp [hzm, range1_eq_zero]
      case pos =>
        conv => rhs
                rw [ List.range_add
                  , range1_eq_zero
                  , List.filter_append
                  , List.sum_append
                  , ← hm ]
        unfold List.filter
        simp; split
        case h_1 hr =>
          apply eq_of_beq at hr
          have := Nat.mul_div_cancel' $ Nat.dvd_of_mod_eq_zero hr
          conv => lhs; simp [List.range_add, range1_eq_zero, Nat.mul_add, this]
          simp; apply Or.inl
          have : m' / n = (m' - 1) / n + 1 := by
            cases m'
            . contradiction
            . simp; exact Nat.succ_div_of_mod_eq_zero hr
          rw [this]
        case h_2 hr =>
          apply ne_of_beq_false at hr
          simp
          apply Or.inl
          have : m' / n = (m' - 1) / n := by
            cases m'
            . contradiction
            . simp; exact Nat.succ_div_of_mod_ne_zero hr
          rw [this]
-- ANCHOR_END: sum_divisible_by_eq_range_filter_sum

-- ANCHOR: proof_sum_divisible_3_5_by_eq_range
theorem sum_divisible_3_5_by_eq_range (n : Nat):
  sum_multiple_3_or_5 n = sum_multiple_3_or_5' n := by
  unfold sum_multiple_3_or_5 sum_multiple_3_or_5'
  simp
  rw [filter_or_sum_eq_filter_add]
  repeat rw [sum_divisible_by_eq_range_filter_sum]
  rw [List.filter_congr λ x a ↦ x_mod_3_and_x_mod_5_eq_mod_15 x]
-- ANCHOR_END: proof_sum_divisible_3_5_by_eq_range
